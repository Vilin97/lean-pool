/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/


import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Real.Pi.Bounds
import LeanPool.OSforGFF.Spacetime.Basic
import LeanPool.OSforGFF.Spacetime.Euclidean
import LeanPool.OSforGFF.Spacetime.DiscreteSymmetry
import LeanPool.OSforGFF.Schwinger.Defs
import LeanPool.OSforGFF.General.FunctionalAnalysis
import LeanPool.OSforGFF.Covariance.Momentum
import LeanPool.OSforGFF.Covariance.Position
import LeanPool.OSforGFF.General.FourierTransforms
import LeanPool.OSforGFF.OS.Axioms
import LeanPool.OSforGFF.Spacetime.ProdIntegrable
import LeanPool.OSforGFF.Spacetime.Decomposition
import LeanPool.OSforGFF.Spacetime.Tonelli
import LeanPool.OSforGFF.General.LaplaceIntegral

/-!
# OS3 Infrastructure — Schwinger Parametrization and Fubini Theorems

The naive Fourier representation of covariance reflection positivity requires exchanging
the k₀ integral with the x,y integrals, but the integrand 1/√(k²+m²) is NOT absolutely
integrable in 3D k-space. The Schwinger parametrization resolves this:

  ⟨Θf, Cf⟩ = ∫₀^∞ e^{−sm²} [∫_x ∫_y f*(x) f(y) H(s, |Θx−y|)] ds

where H(s,r) = (4πs)^{−2} exp(−r²/4s) is the heat kernel, bounded by s^{−2}.
The integrand is absolutely integrable: Schwartz functions are bounded, H is bounded,
and e^{−sm²} provides exponential decay in s.

This file proves the Fubini theorems justifying integration order exchanges between
proper-time s, spatial momenta k_sp, and spacetime points x,y. The integrability
bounds use |f(x)||f(y)| ≤ C · x₀y₀ / (1+|xbar|²)^N(1+|ybar|²)^N for positive-time
test functions, combined with Gaussian moment formulas for the time integrals.
-/

open MeasureTheory Complex Real Filter QFT
open TopologicalSpace
open scoped Real InnerProductSpace BigOperators

noncomputable section

variable {m : ℝ} [Fact (0 < m)]
/-! ## Core Definitions -/

/-- Inner product on spatial coordinates: k_spatial · x_spatial = Σᵢ kᵢ xᵢ -/
noncomputable def spatialDot (k_spatial x_spatial : SpatialCoords) : ℝ :=
  ∑ i, k_spatial i * x_spatial i

/-- Inner product on ℝ equals multiplication. -/
lemma real_inner_eq_mul (x y : ℝ) : @inner ℝ ℝ _ x y = x * y := by
  simp [inner, mul_comm]

/-- spatialDot equals the real inner product on SpatialCoords. -/
lemma spatialDot_eq_inner (k_spatial x_spatial : SpatialCoords) :
    spatialDot k_spatial x_spatial = ⟪k_spatial, x_spatial⟫_ℝ := by
  unfold spatialDot
  rw [PiLp.inner_apply]
  congr 1
  ext i
  rw [real_inner_eq_mul]

/-! ### Shared norm facts for the Fubini integrand factors

The reflection-positivity Fubini integrand is a product of six factors. The following
private lemmas record the norm of each factor; they are reused across the Fubini
integrability and swap proofs below. -/

/-- Norm of the spatial Gaussian factor: `‖exp(-s‖k‖²)‖ = exp(-s‖k‖²)`. -/
private lemma norm_cexp_neg_normSq (s : ℝ) (k : SpatialCoords) :
    ‖Complex.exp (-(s : ℂ) * ‖k‖^2)‖ = Real.exp (-s * ‖k‖^2) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [neg_mul, neg_re, mul_re, Complex.ofReal_re, Complex.ofReal_im]
  have h_im : ((‖k‖ : ℂ) ^ 2).im = 0 := by simp [sq, Complex.mul_im]
  have h_re : ((‖k‖ : ℂ) ^ 2).re = ‖k‖ ^ 2 := by simp [sq, Complex.mul_re]
  simp only [h_im, h_re, mul_zero, sub_zero]

/-- Norm bound for the mass-regularised Gaussian factor:
`‖exp(-s(‖k‖²+m²))‖ ≤ exp(-s·m²)` for `s ≥ 0`. -/
private lemma norm_cexp_neg_normSq_add_le (s m : ℝ) (hs : 0 ≤ s) (k : SpatialCoords) :
    ‖Complex.exp (-(s : ℂ) * (‖k‖^2 + m^2))‖ ≤ Real.exp (-s * m^2) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simp only [neg_mul, neg_re, mul_re, Complex.ofReal_re, Complex.ofReal_im]
  have h_im : (↑‖k‖ ^ 2 + ↑m ^ 2 : ℂ).im = 0 := by simp [sq, Complex.add_im]
  have h_re : (↑‖k‖ ^ 2 + ↑m ^ 2 : ℂ).re = ‖k‖^2 + m^2 := by
    simp only [Complex.add_re, sq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
  simp only [h_im, h_re, mul_zero, sub_zero]
  nlinarith [sq_nonneg ‖k‖]

/-- Norm bound for the heat-kernel factor: `‖exp(-((-a-b)²/(4s)))‖ ≤ 1` for `s ≥ 0`. -/
private lemma norm_cexp_neg_heat_le_one (a b s : ℝ) (hs : 0 ≤ s) :
    ‖Complex.exp (-((-a - b)^2 / (4 * s) : ℝ))‖ ≤ 1 := by
  rw [Complex.norm_exp]
  simp only [neg_re, Complex.ofReal_re]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (div_nonneg (sq_nonneg _) (by linarith)))

/-- Norm of the `√(π/s)` scalar factor cast to `ℂ`. -/
private lemma norm_sqrt_pi_div (s : ℝ) :
    ‖(Real.sqrt (π / s) : ℂ)‖ = Real.sqrt (π / s) := by
  simp [abs_of_nonneg (Real.sqrt_nonneg _)]

/-- Pointwise norm bound for the full mass-regularised Fubini integrand. -/
private lemma cexp6_norm_le_mass (f : TestFunctionℂ) (s m : ℝ) (hs : 0 ≤ s)
    (x y : SpaceTime) (k_sp : SpatialCoords) :
    ‖(starRingEnd ℂ (f x)) * f y *
        (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
        Complex.exp (-(s : ℂ) * (‖k_sp‖^2 + m^2)) *
        Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y))‖ ≤
      ‖f x‖ * ‖f y‖ * Real.sqrt (π / s) * Real.exp (-s * m^2) := by
  have h_star : ‖star (f x)‖ = ‖f x‖ := norm_star _
  have h_exp1 := norm_cexp_neg_heat_le_one (x 0) (y 0) s hs
  have h_exp2 := norm_cexp_neg_normSq_add_le s m hs k_sp
  have h_exp3 := norm_exp_neg_I_mul_real (spatialDot k_sp (spatialPart x - spatialPart y))
  calc ‖(starRingEnd ℂ (f x)) * f y *
          (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
          Complex.exp (-(s : ℂ) * (‖k_sp‖^2 + m^2)) *
          Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y))‖
      ≤ ‖star (f x)‖ * ‖f y‖ * ‖(Real.sqrt (π / s) : ℂ)‖ *
          ‖Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ))‖ *
          ‖Complex.exp (-(s : ℂ) * (‖k_sp‖^2 + m^2))‖ *
          ‖Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y))‖ := by
            simp only [norm_mul, starRingEnd_apply, le_refl]
    _ ≤ ‖f x‖ * ‖f y‖ * Real.sqrt (π / s) * 1 * Real.exp (-s * m^2) * 1 := by
        rw [h_star, norm_sqrt_pi_div, h_exp3]
        gcongr
    _ = ‖f x‖ * ‖f y‖ * Real.sqrt (π / s) * Real.exp (-s * m^2) := by ring

/-- Pointwise norm bound for the full spatial-momentum Fubini integrand. -/
private lemma cexp6_norm_le_ksp (f : TestFunctionℂ) (s : ℝ) (hs : 0 ≤ s)
    (x y : SpaceTime) (k_sp : SpatialCoords) :
    ‖(starRingEnd ℂ (f x)) * f y *
        (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
        Complex.exp (-(s : ℂ) * ‖k_sp‖^2) *
        Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y))‖ ≤
      ‖f x‖ * ‖f y‖ * Real.sqrt (π / s) * Real.exp (-s * ‖k_sp‖^2) := by
  have h_star : ‖star (f x)‖ = ‖f x‖ := norm_star _
  have h_exp1 := norm_cexp_neg_heat_le_one (x 0) (y 0) s hs
  have h_exp2 := norm_cexp_neg_normSq s k_sp
  have h_exp3 := norm_exp_neg_I_mul_real (spatialDot k_sp (spatialPart x - spatialPart y))
  calc ‖(starRingEnd ℂ (f x)) * f y *
          (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
          Complex.exp (-(s : ℂ) * ‖k_sp‖^2) *
          Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y))‖
      ≤ ‖star (f x)‖ * ‖f y‖ * ‖(Real.sqrt (π / s) : ℂ)‖ *
          ‖Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ))‖ *
          ‖Complex.exp (-(s : ℂ) * ‖k_sp‖^2)‖ *
          ‖Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y))‖ := by
            simp only [norm_mul, starRingEnd_apply, le_refl]
    _ ≤ ‖f x‖ * ‖f y‖ * Real.sqrt (π / s) * 1 * Real.exp (-s * ‖k_sp‖^2) * 1 := by
        rw [h_star, norm_sqrt_pi_div, h_exp2, h_exp3]
        gcongr
    _ = ‖f x‖ * ‖f y‖ * Real.sqrt (π / s) * Real.exp (-s * ‖k_sp‖^2) := by ring

/-- The inner product on SpaceTime decomposes into time and spatial parts:
    ⟪k, z⟫ = k₀ z₀ + ⟪k_sp, z_sp⟫ = k₀ z₀ + spatialDot(k_sp, z_sp)
-/
lemma spacetime_inner_decompose (k z : SpaceTime) :
    ⟪k, z⟫_ℝ = k 0 * z 0 + spatialDot (spatialPart k) (spatialPart z) := by
  unfold spatialDot spatialPart
  rw [PiLp.inner_apply]
  -- Convert inner products to multiplications
  simp only [real_inner_eq_mul]
  -- The sum over Fin 4 decomposes into index 0 plus sum over indices 1,2,3
  conv_lhs => rw [Fin.sum_univ_succ]
  -- The sums are definitionally equal after unfolding
  congr 1

/-! ### Integral Decomposition for SpaceTime -/

/-- Auxiliary: The weighted Laplace-Fourier transform appearing in reflection positivity.
    F_ω(k_spatial) = ∫ dx f(x) exp(-|x₀| ω(k)) exp(i k_spatial · x_spatial)

    This is the key quantity that appears after contour integration. For functions
    supported on positive time (x₀ ≥ 0), this becomes a product of two Fourier-Laplace
    transforms, leading to the squared norm factorization.
-/
noncomputable def weightedLaplaceFourier (m : ℝ) (f : TestFunctionℂ) (k_spatial : SpatialCoords) :
  ℂ :=
  let ω := Real.sqrt (‖k_spatial‖^2 + m^2)
  ∫ x : SpaceTime, f x * Complex.exp (-|x 0| * ω) *
    Complex.exp (Complex.I * spatialDot k_spatial (spatialPart x))

/-! ## Time Reflection Properties -/

/-- Time reflection is measure-preserving (it's a linear isometry). -/
lemma timeReflection_measurePreserving :
  MeasurePreserving timeReflection (volume : Measure SpaceTime) volume :=
  timeReflectionLE.measurePreserving

/-- Time reflection is an involution: Θ(Θx) = x -/
lemma timeReflection_involutive (x : SpaceTime) :
    timeReflection (timeReflection x) = x := by
  simp [timeReflection, Function.update]

/-! ## Mixed Representation and k₀-inside Form

The key step in the reflection positivity proof is to convert the Bessel bilinear form
to a momentum representation where the k₀ integral is innermost.

**Important mathematical point**: The naive d⁴k momentum integral does NOT converge
as a Lebesgue integral (it decays like 1/k² which is not integrable in 4D).
The correct procedure uses the "mixed representation" of the Bessel kernel:

    C(x,y) = (1/(2(2π)^{d-1})) ∫_{k_sp} (1/ω) exp(-ω|x₀-y₀|) exp(-i k_sp·(x_sp-y_sp))

This mixed form has:
- Time dependence in position space: exp(-ω|t|) (exponential decay)
- Spatial dependence in momentum space: exp(-i k_sp·r_sp)

The crucial observation is that by `fourier_lorentzian_1d_neg`:
    (π/ω) exp(-ω|t|) = ∫_{k₀} exp(-ik₀t)/(k₀²+ω²) dk₀

So (1/ω) exp(-ω|t|) = (1/π) ∫_{k₀} exp(-ik₀t)/(k₀²+ω²) dk₀

This allows us to convert between:
- Mixed representation: with exp(-ω|t|) evaluated
- k₀-inside form: with ∫_{k₀} 1/(k₀²+ω²) unevaluated
-/

/-! ## Laplace Integral Identity

The key mathematical identity underlying the mixed representation is:

    ∫₀^∞ s^{-1/2} exp(-a/s - bs) ds = √(π/b) exp(-2√(ab))  for a, b > 0

This is a standard result (modified Bessel K_{1/2}) that appears when computing
the spatial Fourier transform of the heat kernel integrated against proper time.

**Derivation sketch:**
The substitution u = √(a/b) exp(t) transforms this into an integral related to K_{1/2}.
Since K_{1/2}(z) = √(π/(2z)) exp(-z), the identity follows.
-/

/-- **d-dimensional Gaussian Fourier transform.**

    For d = 4, this states:
    (1/(2π)^4) ∫_{ℝ^4} exp(-ik·z) exp(-s|k|²) d⁴k = (4πs)^{-2} exp(-|z|²/(4s))

    which equals `heatKernelPositionSpace s |z|`.

    **Proof:**
    Uses Mathlib's `integral_cexp_neg_mul_sq_norm_add` with b = s, c = -I, w = z:
    ∫ k, exp(-s‖k‖² + (-I)⟪z,k⟫) = (π/s)^{d/2} * exp((-I)²‖z‖²/(4s))
                                  = (π/s)^{d/2} * exp(-‖z‖²/(4s))

    Combined with the normalization (1/(2π)^d) and the heat kernel formula:
    (1/(2π)^d) * (π/s)^{d/2} = (4πs)^{-d/2}
-/
theorem heatKernel_eq_gaussianFT (s : ℝ) (hs : 0 < s) (z : SpaceTime) :
    (heatKernelPositionSpace s ‖z‖ : ℂ) =
    (1 / (2 * π) ^ STDimension : ℝ) *
    ∫ k : SpaceTime, Complex.exp (-Complex.I * ⟪k, z⟫_ℝ) * Complex.exp (-(s : ℂ) * ‖k‖^2) := by
  -- Step 1: Rewrite the integral as ∫ exp(-s‖k‖² - I⟪k,z⟫) = ∫ exp(-s‖k‖² + (-I)⟪z,k⟫)
  have h_integral : ∫ k : SpaceTime, Complex.exp (-Complex.I * ⟪k, z⟫_ℝ) *
      Complex.exp (-(s : ℂ) * ‖k‖^2) =
      ∫ k : SpaceTime, Complex.exp (-(s : ℂ) * ‖k‖^2 + (-Complex.I) * ⟪z, k⟫_ℝ) := by
    congr 1
    ext k
    rw [← Complex.exp_add]
    congr 1
    -- ⟪k, z⟫ = ⟪z, k⟫ by symmetry of inner product
    have h_sym : ⟪k, z⟫_ℝ = ⟪z, k⟫_ℝ := (real_inner_comm k z).symm
    rw [h_sym]
    ring
  rw [h_integral]
  -- Step 2: Apply Mathlib's integral_cexp_neg_mul_sq_norm_add
  have hs_re : 0 < (s : ℂ).re := by simp [hs]
  have h_main := GaussianFourier.integral_cexp_neg_mul_sq_norm_add (V := SpaceTime) hs_re
    (-Complex.I) z
  rw [h_main]
  -- Step 3: Simplify (-I)² = -1
  have h_I_sq : (-Complex.I) ^ 2 = -1 := by
    rw [neg_sq, Complex.I_sq]
  simp only [h_I_sq, neg_one_mul]
  -- Step 4: Verify the coefficient equality
  -- Need: (4πs)^{-d/2} exp(-‖z‖²/(4s)) = (1/(2π)^d) * (π/s)^{d/2} * exp(-‖z‖²/(4s))
  -- For d = 4: (4πs)^{-2} = (1/(2π)^4) * (π/s)^2
  -- LHS = 1/(16π²s²)
  -- RHS = 1/(16π⁴) * π²/s² = 1/(16π²s²) ✓
  -- Expand heatKernelPositionSpace
  rw [heatKernelPositionSpace_4D s hs ‖z‖]
  -- The finrank of SpaceTime is 4
  have h_finrank : Module.finrank ℝ SpaceTime = 4 := finrank_euclideanSpace_fin
  rw [h_finrank]
  -- Simplify the complex exponent ↑4 / 2 = 2
  have h_exp_eq : (↑π / ↑s : ℂ) ^ ((4 : ℕ) / 2 : ℂ) = (↑π / ↑s : ℂ) ^ (2 : ℂ) := by
    congr 1
    norm_num
  rw [h_exp_eq]
  -- (π/s)^2 as complex power equals (π/s)² as a natural power
  have h_pow_div : (↑π / ↑s : ℂ) = ↑(π / s) := by push_cast; ring
  rw [h_pow_div]
  -- Convert complex power (2 : ℂ) to natural power
  have h_cpow_two : (↑(π / s) : ℂ) ^ (2 : ℂ) = (↑(π / s) : ℂ) ^ (2 : ℕ) := Complex.cpow_natCast _ 2
  rw [h_cpow_two]
  -- Now combine everything
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hs_ne : s ≠ 0 := ne_of_gt hs
  have hd : (STDimension : ℕ) = 4 := rfl
  simp only [hd, pow_two]
  push_cast
  field_simp
  ring

/-! ### Technical Integration Lemmas

The following lemmas establish integrability and measurability conditions
that are mathematically standard but require substantial Mathlib plumbing.
-/

/-- The heat kernel is jointly continuous on (0, ∞) × ℝ as a function of (t, r). -/
lemma heatKernelPositionSpace_continuousOn :
    ContinuousOn (fun p : ℝ × ℝ => heatKernelPositionSpace p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.univ) := by
  unfold heatKernelPositionSpace
  apply ContinuousOn.mul
  · -- (4 * π * t) ^ (-(d : ℝ) / 2) is continuous for t > 0
    apply ContinuousOn.rpow
    · apply ContinuousOn.mul continuousOn_const
      exact continuousOn_fst
    · exact continuousOn_const
    · intro ⟨t, _⟩ ⟨ht, _⟩
      left
      simp only [Set.mem_Ioi] at ht
      positivity
  · -- exp(-r²/(4t)) is continuous for t > 0
    apply Real.continuous_exp.comp_continuousOn
    -- Need: ContinuousOn (fun p => -p.2^2 / (4 * p.1)) (Ioi 0 ×ˢ univ)
    -- Rewrite as (-1) * (p.2^2 / (4 * p.1))
    have h_eq : (fun p : ℝ × ℝ => -p.2 ^ 2 / (4 * p.1)) =
        (fun p : ℝ × ℝ => (-1) * (p.2 ^ 2 / (4 * p.1))) := by ext; ring
    rw [h_eq]
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.div
    · apply ContinuousOn.pow
      exact continuousOn_snd
    · apply ContinuousOn.mul continuousOn_const
      exact continuousOn_fst
    · intro ⟨t, _⟩ ⟨ht, _⟩
      simp only [Set.mem_Ioi] at ht
      simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]; exact ht.ne'

/-- The real heat-kernel composition `p ↦ H(p.1, ‖Θ p.2.1 - p.2.2‖)` is continuous on the
    support `Ioi 0 ×ˢ univ`. Shared core of the two `aestronglyMeasurable` theorems below. -/
private lemma heatKernelPositionSpace_comp_continuousOn :
    ContinuousOn
      (fun p : ℝ × SpaceTime × SpaceTime =>
        heatKernelPositionSpace p.1 ‖timeReflection p.2.1 - p.2.2‖)
      (Set.Ioi 0 ×ˢ Set.univ) := by
  have h_norm : Continuous (fun p : ℝ × SpaceTime × SpaceTime =>
      ‖timeReflection p.2.1 - p.2.2‖) :=
    continuous_norm.comp <| ((LinearIsometryEquiv.continuous timeReflectionLE).comp
      (continuous_fst.comp continuous_snd)).sub (continuous_snd.comp continuous_snd)
  have h_proj : ContinuousOn
      (fun p : ℝ × SpaceTime × SpaceTime => (p.1, ‖timeReflection p.2.1 - p.2.2‖))
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) :=
    ContinuousOn.prodMk continuousOn_fst h_norm.continuousOn
  have h_maps : Set.MapsTo
      (fun p : ℝ × SpaceTime × SpaceTime => (p.1, ‖timeReflection p.2.1 - p.2.2‖))
      (Set.Ioi 0 ×ˢ Set.univ) (Set.Ioi 0 ×ˢ Set.univ) :=
    fun _ ⟨hs, _⟩ => ⟨hs, Set.mem_univ _⟩
  exact heatKernelPositionSpace_continuousOn.comp h_proj h_maps

/-- **Heat kernel composition is AEStronglyMeasurable.**

    The function `p ↦ heatKernelPositionSpace p.1 ‖timeReflection p.2.1 - p.2.2‖`
    is AEStronglyMeasurable with respect to the restricted product measure
    `(volume.restrict (Set.Ioi 0)).prod (volume.prod volume)`. -/
theorem heatKernelPositionSpace_aestronglyMeasurable :
    AEStronglyMeasurable
      (fun p : ℝ × SpaceTime × SpaceTime =>
        (heatKernelPositionSpace p.1 ‖timeReflection p.2.1 - p.2.2‖ : ℂ))
      ((volume.restrict (Set.Ioi 0)).prod (volume.prod volume)) := by
  rw [Measure.restrict_prod_eq_prod_univ (Set.Ioi (0 : ℝ))]
  exact (Complex.continuous_ofReal.comp_continuousOn
    heatKernelPositionSpace_comp_continuousOn).aestronglyMeasurable
    (measurableSet_Ioi.prod MeasurableSet.univ)

/-- Real-valued version of `heatKernelPositionSpace_aestronglyMeasurable`. -/
theorem heatKernelPositionSpace_aestronglyMeasurable_real :
    AEStronglyMeasurable
      (fun p : ℝ × SpaceTime × SpaceTime =>
        heatKernelPositionSpace p.1 ‖timeReflection p.2.1 - p.2.2‖)
      ((volume.restrict (Set.Ioi 0)).prod (volume.prod volume)) := by
  rw [Measure.restrict_prod_eq_prod_univ (Set.Ioi (0 : ℝ))]
  exact heatKernelPositionSpace_comp_continuousOn.aestronglyMeasurable
    (measurableSet_Ioi.prod MeasurableSet.univ)

/-- The heat kernel integral is translation invariant:
    ∫_y H(s, ‖a - y‖) dy = ∫_z H(s, ‖z‖) dz = 1 for any a ∈ SpaceTime.

    This follows from:
    1. Lebesgue measure on SpaceTime is translation invariant
    2. The norm satisfies ‖a - y‖ = ‖-(y - a)‖ = ‖y - a‖
    3. The heat kernel integrates to 1 (heatKernelPositionSpace_integral_eq_one)
-/
lemma heatKernelPositionSpace_integral_translated (s : ℝ) (hs : 0 < s) (a : SpaceTime) :
    ∫ y : SpaceTime, heatKernelPositionSpace s ‖a - y‖ = 1 := by
  -- First, ‖a - y‖ = ‖y - a‖ (norm is symmetric under negation)
  have h_norm_eq : ∀ y, ‖a - y‖ = ‖y - a‖ := fun y => by
    rw [← neg_sub, norm_neg]
  have h_fun : (fun y : SpaceTime => heatKernelPositionSpace s ‖a - y‖) =
      (fun y : SpaceTime => heatKernelPositionSpace s ‖y - a‖) := by
    funext y
    rw [h_norm_eq y]
  rw [h_fun]
  -- Use translation invariance: ∫ f(y - a) dy = ∫ f(z) dz
  -- SpaceTime = EuclideanSpace ℝ (Fin 4) has translation-invariant Lebesgue measure
  have h_transl := @MeasureTheory.integral_sub_right_eq_self SpaceTime ℝ _ _ _
    (volume : Measure SpaceTime) _ _ _
    (fun z => heatKernelPositionSpace s ‖z‖) a
  rw [h_transl]
  -- Now apply the normalization lemma
  exact heatKernelPositionSpace_integral_eq_one s hs

/-- The translated heat kernel is integrable (since its integral equals 1). -/
lemma heatKernelPositionSpace_integrable (s : ℝ) (hs : 0 < s) (a : SpaceTime) :
    Integrable (fun y : SpaceTime => heatKernelPositionSpace s ‖a - y‖)
      (volume : Measure SpaceTime) := by
  apply integrable_of_integral_eq_one
  exact heatKernelPositionSpace_integral_translated s hs a

/-- Nonnegativity of the Schwinger bound integrand (fixed s > 0). -/
lemma schwinger_bound_integrand_nonneg (s : ℝ) (hs : 0 < s)
    (f : TestFunctionℂ) (Cf : ℝ) (hCf_nonneg : 0 ≤ Cf) (m : ℝ) (x y : SpaceTime) :
  0 ≤ ‖f x‖ * Cf * Real.exp (-s * m^2) *
      heatKernelPositionSpace s ‖timeReflection x - y‖ := by
  apply mul_nonneg
  · apply mul_nonneg
    · apply mul_nonneg
      · exact norm_nonneg _
      · exact hCf_nonneg
    · exact Real.exp_nonneg _
  · exact heatKernelPositionSpace_nonneg s hs ‖timeReflection x - y‖

/-- Integrability in `y` of the Schwinger bound integrand for fixed `s > 0`, `x`. -/
lemma schwinger_bound_integrand_integrable_y (s : ℝ) (hs : 0 < s)
    (f : TestFunctionℂ) (Cf : ℝ) (m : ℝ) (x : SpaceTime) :
    Integrable (fun y : SpaceTime =>
      (‖f x‖ * Cf * Real.exp (-s * m^2)) *
        heatKernelPositionSpace s ‖timeReflection x - y‖)
      (volume : Measure SpaceTime) := by
  have hH : Integrable (fun y : SpaceTime =>
      heatKernelPositionSpace s ‖timeReflection x - y‖) :=
    heatKernelPositionSpace_integrable s hs (timeReflection x)
  exact hH.const_mul (‖f x‖ * Cf * Real.exp (-s * m^2))

/-- Evaluate the `y`-integral of the Schwinger bound integrand for fixed `s > 0`, `x`. -/
lemma schwinger_bound_integrand_integral_y (s : ℝ) (hs : 0 < s)
    (f : TestFunctionℂ) (Cf : ℝ) (m : ℝ) (x : SpaceTime) :
    ∫ y : SpaceTime,
        (‖f x‖ * Cf * Real.exp (-s * m^2)) *
          heatKernelPositionSpace s ‖timeReflection x - y‖ =
      ‖f x‖ * Cf * Real.exp (-s * m^2) := by
  let r : ℝ := (‖f x‖ * Cf) * Real.exp (-s * m^2)
  have h_eq : ∫ y : SpaceTime, r *
        heatKernelPositionSpace s ‖timeReflection x - y‖ =
      r * ∫ y : SpaceTime, heatKernelPositionSpace s ‖timeReflection x - y‖ := by
    simpa using
      (integral_const_mul r
        (fun y : SpaceTime => heatKernelPositionSpace s ‖timeReflection x - y‖))
  have h_int : ∫ y : SpaceTime, heatKernelPositionSpace s ‖timeReflection x - y‖ = 1 :=
    heatKernelPositionSpace_integral_translated s hs (timeReflection x)
  simpa [r, h_int, mul_assoc] using h_eq

/-- Integrability in `x` of the Schwinger bound integrand (after integrating in `y`). -/
lemma schwinger_bound_integrand_integrable_x (s : ℝ)
    (f : TestFunctionℂ) (Cf : ℝ) (m : ℝ)
    (h_f_int : Integrable (fun x => ‖f x‖) (volume : Measure SpaceTime)) :
    Integrable (fun x : SpaceTime => ‖f x‖ * Cf * Real.exp (-s * m^2))
      (volume : Measure SpaceTime) := by
  have h := h_f_int.mul_const (Cf * Real.exp (-s * m^2))
  simpa [mul_assoc] using h

/-- Integrability of the Schwinger bound integrand on `(x,y)` for fixed `s > 0`. -/
lemma schwinger_bound_integrable_xy (s : ℝ) (hs : 0 < s)
    (f : TestFunctionℂ) (Cf : ℝ) (m : ℝ) (hCf_nonneg : 0 ≤ Cf)
    (h_f_int : Integrable (fun x => ‖f x‖) (volume : Measure SpaceTime)) :
    Integrable
      (fun p : SpaceTime × SpaceTime =>
        ‖f p.1‖ * Cf * Real.exp (-s * m^2) *
          heatKernelPositionSpace s ‖timeReflection p.1 - p.2‖)
      (volume.prod volume) := by
  -- Use integrable_prod_iff on (x,y)
  let G : SpaceTime × SpaceTime → ℝ := fun p =>
    ‖f p.1‖ * Cf * Real.exp (-s * m^2) *
      heatKernelPositionSpace s ‖timeReflection p.1 - p.2‖
  have hG_meas : AEStronglyMeasurable G (volume.prod volume) := by
    have h_fG : AEStronglyMeasurable (fun p : SpaceTime × SpaceTime => ‖f p.1‖)
        (volume.prod volume) := by
      have hf_cont : Continuous (fun p : SpaceTime × SpaceTime => f p.1) :=
        (SchwartzMap.continuous f).comp continuous_fst
      exact hf_cont.aestronglyMeasurable.norm
    have h_heatG : AEStronglyMeasurable
        (fun p : SpaceTime × SpaceTime =>
          heatKernelPositionSpace s ‖timeReflection p.1 - p.2‖)
        (volume.prod volume) := by
      have h_norm : Continuous (fun p : SpaceTime × SpaceTime =>
          ‖timeReflection p.1 - p.2‖) := by
        apply continuous_norm.comp
        apply Continuous.sub
        · exact (LinearIsometryEquiv.continuous timeReflectionLE).comp continuous_fst
        · exact continuous_snd
      have h_cont_r : Continuous (fun r : ℝ => heatKernelPositionSpace s r) := by
        have h_cont_on : ContinuousOn (fun r : ℝ => heatKernelPositionSpace s r) Set.univ := by
          have h_proj : ContinuousOn (fun r : ℝ => (s, r)) Set.univ := by
            exact (continuous_const.prodMk continuous_id).continuousOn
          have h_maps : Set.MapsTo (fun r : ℝ => (s, r)) Set.univ (Set.Ioi 0 ×ˢ Set.univ) := by
            intro r _; exact ⟨hs, Set.mem_univ _⟩
          exact heatKernelPositionSpace_continuousOn.comp h_proj h_maps
        exact (continuousOn_univ.mp h_cont_on)
      exact (h_cont_r.comp h_norm).aestronglyMeasurable
    have h_fCexp : AEStronglyMeasurable
        (fun p : SpaceTime × SpaceTime => (‖f p.1‖ * Cf) * Real.exp (-s * m^2))
        (volume.prod volume) :=
      (h_fG.mul_const Cf).mul_const (Real.exp (-s * m^2))
    have h_all : AEStronglyMeasurable G (volume.prod volume) :=
      h_fCexp.mul h_heatG
    simpa [G, mul_assoc, mul_left_comm, mul_comm] using h_all
  refine (MeasureTheory.integrable_prod_iff (μ := volume) (ν := volume) hG_meas).2 ?_
  constructor
  · refine Eventually.of_forall ?_
    intro x
    exact schwinger_bound_integrand_integrable_y s hs f Cf m x
  · -- integrable in x of the norm-integral
    have h_norm : ∀ x : SpaceTime,
        ∫ y : SpaceTime, ‖G (x, y)‖ = ‖f x‖ * Cf * Real.exp (-s * m^2) := by
      intro x
      have h_eq : (fun y : SpaceTime => ‖G (x, y)‖) =
          (fun y : SpaceTime => (‖f x‖ * Cf * Real.exp (-s * m^2)) *
            heatKernelPositionSpace s ‖timeReflection x - y‖) := by
        funext y
        have hy : 0 ≤ G (x, y) :=
          schwinger_bound_integrand_nonneg s hs f Cf hCf_nonneg m x y
        have : ‖G (x, y)‖ = G (x, y) := by
          simpa using (Real.norm_of_nonneg hy)
        simpa [G, this, mul_assoc]
      calc
        ∫ y : SpaceTime, ‖G (x, y)‖
            = ∫ y : SpaceTime,
                (‖f x‖ * Cf * Real.exp (-s * m^2)) *
                  heatKernelPositionSpace s ‖timeReflection x - y‖ := by
                exact integral_congr_ae (by
                  filter_upwards with y
                  have h := congrArg (fun h => h y) h_eq
                  simpa using h)
        _ = (‖f x‖ * Cf * Real.exp (-s * m^2)) :=
              schwinger_bound_integrand_integral_y s hs f Cf m x
    have h_int_x : Integrable (fun x : SpaceTime => ‖f x‖ * Cf * Real.exp (-s * m^2)) :=
      schwinger_bound_integrand_integrable_x s f Cf m h_f_int
    exact h_int_x.congr (by
      filter_upwards with x
      have h := h_norm x
      have h' : ∫ y : SpaceTime, |G (x, y)| = ‖f x‖ * Cf * Real.exp (-s * m^2) := by
        simpa [Real.norm_eq_abs] using h
      exact h'.symm)

/-- Compute the (x,y)-integral of the Schwinger bound integrand for fixed `s > 0`. -/
lemma schwinger_bound_integrand_integral_xy (s : ℝ) (hs : 0 < s)
    (f : TestFunctionℂ) (Cf : ℝ) (m : ℝ) (hCf_nonneg : 0 ≤ Cf)
    (h_f_int : Integrable (fun x => ‖f x‖) (volume : Measure SpaceTime)) :
    ∫ p : SpaceTime × SpaceTime,
      ‖f p.1‖ * Cf * Real.exp (-s * m^2) *
        heatKernelPositionSpace s ‖timeReflection p.1 - p.2‖ =
      (Cf * (∫ x : SpaceTime, ‖f x‖)) * Real.exp (-s * m^2) := by
  let G : SpaceTime × SpaceTime → ℝ := fun p =>
    ‖f p.1‖ * Cf * Real.exp (-s * m^2) *
      heatKernelPositionSpace s ‖timeReflection p.1 - p.2‖
  have hG_int : Integrable G (volume.prod volume) :=
    schwinger_bound_integrable_xy s hs f Cf m hCf_nonneg h_f_int
  have h_prod := MeasureTheory.integral_prod (μ := volume) (ν := volume) (f := G) hG_int
  -- rewrite using the y-integral formula
  have h_inner : ∀ x : SpaceTime,
      ∫ y : SpaceTime, G (x, y) = ‖f x‖ * Cf * Real.exp (-s * m^2) := by
    intro x
    simpa [G] using schwinger_bound_integrand_integral_y s hs f Cf m x
  calc
    ∫ p : SpaceTime × SpaceTime, G p
        = ∫ x : SpaceTime, ∫ y : SpaceTime, G (x, y) := by
            rwa [Measure.volume_eq_prod]
    _ = ∫ x : SpaceTime, ‖f x‖ * Cf * Real.exp (-s * m^2) := by
          refine integral_congr_ae ?_
          filter_upwards with x
          simp [h_inner]
    _ = (Cf * (∫ x : SpaceTime, ‖f x‖)) * Real.exp (-s * m^2) := by
          -- pull out the constant
          let r : ℝ := Cf * Real.exp (-s * m^2)
          have h_eq : ∫ x : SpaceTime, r * ‖f x‖ = r * ∫ x : SpaceTime, ‖f x‖ := by
            simpa using (integral_const_mul r (fun x : SpaceTime => ‖f x‖))
          simpa [r, mul_comm, mul_left_comm, mul_assoc] using h_eq

/-- Fubini/Tonelli step for Schwinger bound integrability. -/
theorem schwinger_bound_integrable_fubini (m : ℝ) [Fact (0 < m)] (f : TestFunctionℂ)
    (Cf : ℝ) (hCf : ∀ x, ‖f x‖ ≤ Cf)
    (h_f_int : Integrable (fun x => ‖f x‖) (volume : Measure SpaceTime))
    (hCf_nonneg : 0 ≤ Cf)
    (h_y_eq_one : ∀ s > 0, ∀ x : SpaceTime,
        ∫ y : SpaceTime, heatKernelPositionSpace s ‖timeReflection x - y‖ = 1)
    (h_exp_int : ∫ s in Set.Ioi 0, Real.exp (-s * m^2) = 1 / m^2) :
    Integrable
      (fun p : ℝ × SpaceTime × SpaceTime =>
        ‖f p.2.1‖ * Cf * Real.exp (-p.1 * m^2) *
          heatKernelPositionSpace p.1 ‖timeReflection p.2.1 - p.2.2‖)
      ((volume.restrict (Set.Ioi 0)).prod (volume.prod volume)) := by
  classical
  -- Mark unused parameters as used (they are part of the hypotheses contract).
  have _ := hCf
  have _ := h_y_eq_one
  let F : ℝ × SpaceTime × SpaceTime → ℝ := fun p =>
    ‖f p.2.1‖ * Cf * Real.exp (-p.1 * m^2) *
      heatKernelPositionSpace p.1 ‖timeReflection p.2.1 - p.2.2‖
  have h_meas : AEStronglyMeasurable F
      ((volume.restrict (Set.Ioi 0)).prod (volume.prod volume)) := by
    have h_f : AEStronglyMeasurable (fun p : ℝ × SpaceTime × SpaceTime => ‖f p.2.1‖)
        ((volume.restrict (Set.Ioi 0)).prod (volume.prod volume)) := by
      have hf_cont : Continuous (fun p : ℝ × SpaceTime × SpaceTime => f p.2.1) :=
        (SchwartzMap.continuous f).comp (continuous_snd.fst)
      exact hf_cont.aestronglyMeasurable.norm
    have h_exp : AEStronglyMeasurable (fun p : ℝ × SpaceTime × SpaceTime =>
        Real.exp (-p.1 * m^2)) ((volume.restrict (Set.Ioi 0)).prod (volume.prod volume)) := by
      have h_cont : Continuous (fun p : ℝ × SpaceTime × SpaceTime => Real.exp (-p.1 * m^2)) :=
        (Real.continuous_exp.comp (continuous_fst.neg.mul continuous_const))
      exact h_cont.aestronglyMeasurable
    have h_heat : AEStronglyMeasurable
        (fun p : ℝ × SpaceTime × SpaceTime =>
          heatKernelPositionSpace p.1 ‖timeReflection p.2.1 - p.2.2‖)
        ((volume.restrict (Set.Ioi 0)).prod (volume.prod volume)) :=
      heatKernelPositionSpace_aestronglyMeasurable_real
    have h_fCexp : AEStronglyMeasurable
        (fun p : ℝ × SpaceTime × SpaceTime => (‖f p.2.1‖ * Cf) * Real.exp (-p.1 * m^2))
        ((volume.restrict (Set.Ioi 0)).prod (volume.prod volume)) :=
      (h_f.mul_const Cf).mul h_exp
    have h_all : AEStronglyMeasurable
        (fun p : ℝ × SpaceTime × SpaceTime =>
          (‖f p.2.1‖ * Cf) * Real.exp (-p.1 * m^2) *
            heatKernelPositionSpace p.1 ‖timeReflection p.2.1 - p.2.2‖)
        ((volume.restrict (Set.Ioi 0)).prod (volume.prod volume)) :=
      h_fCexp.mul h_heat
    simpa [F, mul_assoc, mul_left_comm, mul_comm] using h_all
  refine (MeasureTheory.integrable_prod_iff (μ := volume.restrict (Set.Ioi 0))
    (ν := volume.prod volume) h_meas).2 ?_
  constructor
  · refine (ae_restrict_mem measurableSet_Ioi).mono ?_
    intro s hs
    have hs' : 0 < s := hs
    exact schwinger_bound_integrable_xy s hs' f Cf m hCf_nonneg h_f_int
  · -- integrable of s ↦ ∫_{x,y} ‖F(s,x,y)‖
    have h_exp_ne_zero : (∫ s in Set.Ioi 0, Real.exp (-s * m^2)) ≠ 0 := by
      rw [h_exp_int]
      have hm : m ≠ 0 := ne_of_gt (Fact.out : 0 < m)
      exact one_div_ne_zero (pow_ne_zero 2 hm)
    have h_exp_intg : Integrable (fun s : ℝ => Real.exp (-s * m^2))
        (volume.restrict (Set.Ioi 0)) :=
      Integrable.of_integral_ne_zero h_exp_ne_zero
    have h_const : Integrable (fun s : ℝ => (Cf * (∫ x : SpaceTime, ‖f x‖)) *
        Real.exp (-s * m^2)) (volume.restrict (Set.Ioi 0)) := by
      have h := h_exp_intg.const_mul (Cf * (∫ x : SpaceTime, ‖f x‖))
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    refine h_const.congr ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono ?_
    intro s hs
    have hs' : 0 < s := hs
    have h_eq_norm :
        ∫ p : SpaceTime × SpaceTime, ‖F (s, p.1, p.2)‖ =
          ∫ p : SpaceTime × SpaceTime,
            ‖f p.1‖ * Cf * Real.exp (-s * m^2) *
              heatKernelPositionSpace s ‖timeReflection p.1 - p.2‖ := by
      refine integral_congr_ae ?_
      filter_upwards with p
      have h_nonneg' : 0 ≤ F (s, p.1, p.2) := by
        simpa [F] using
          schwinger_bound_integrand_nonneg s hs' f Cf hCf_nonneg m p.1 p.2
      have : ‖F (s, p.1, p.2)‖ = F (s, p.1, p.2) := by
        simpa using (Real.norm_of_nonneg h_nonneg')
      simpa [F, this, mul_assoc]
    have h_eq :
        ∫ p : SpaceTime × SpaceTime, ‖F (s, p.1, p.2)‖ =
          (Cf * (∫ x : SpaceTime, ‖f x‖)) * Real.exp (-s * m^2) := by
      calc
        ∫ p : SpaceTime × SpaceTime, ‖F (s, p.1, p.2)‖
            = ∫ p : SpaceTime × SpaceTime,
                ‖f p.1‖ * Cf * Real.exp (-s * m^2) *
                  heatKernelPositionSpace s ‖timeReflection p.1 - p.2‖ := h_eq_norm
        _ = (Cf * (∫ x : SpaceTime, ‖f x‖)) * Real.exp (-s * m^2) :=
              schwinger_bound_integrand_integral_xy s hs' f Cf m hCf_nonneg h_f_int
    exact h_eq.symm

/-- **Bound function for Schwinger integrability is integrable.**

    For any Schwartz function f and mass m > 0, the bound
    `p ↦ ‖f p.2.1‖ * ‖f‖_∞ * exp(-p.1 * m²) * H(p.1, ‖Θ p.2.1 - p.2.2‖)`
    is integrable on `(Ioi 0) × SpaceTime × SpaceTime`.

    **Proof structure:**
    Using Tonelli's theorem in the order (y, x, s):
    1. ∫_y H(s, ‖Θx - y‖) dy = 1 (heat kernel L¹ normalization by translation)
    2. ∫_x ‖f x‖ dx = ‖f‖_{L¹} < ∞ (Schwartz integrability)
    3. ∫_s exp(-sm²) ds = 1/m² < ∞ (exponential decay)
    Total: ‖f‖_∞ × ‖f‖_{L¹} / m² < ∞

    The proof combines:
    - `heatKernelPositionSpace_integral_translated` for heat kernel normalization
    - `SchwartzMap.integrable` for Schwartz L¹ integrability
    - `integral_exp_neg_mul_Ioi_eq_inv` for exponential integral

    The proof delegates to `schwinger_bound_integrable_fubini` for the technical Tonelli step.
-/
theorem schwinger_bound_integrable (m : ℝ) [Fact (0 < m)] (f : TestFunctionℂ)
    (Cf : ℝ) (hCf : ∀ x, ‖f x‖ ≤ Cf) :
    Integrable
      (fun p : ℝ × SpaceTime × SpaceTime =>
        ‖f p.2.1‖ * Cf * Real.exp (-p.1 * m^2) *
          heatKernelPositionSpace p.1 ‖timeReflection p.2.1 - p.2.2‖)
      ((volume.restrict (Set.Ioi 0)).prod (volume.prod volume)) := by
  -- Mass positivity
  have hm : 0 < m := Fact.out
  have h_f_int : Integrable (fun x => ‖f x‖) (volume : Measure SpaceTime) :=
    f.integrable.norm
  have h_exp_int : ∫ s in Set.Ioi 0, Real.exp (-s * m^2) = 1 / m^2 := by
    have := integral_exp_neg_mul_Ioi_eq_inv (m^2) (sq_pos_of_pos hm)
    simp only [one_div] at this ⊢
    convert this using 2
    ext s; ring_nf
  have h_y_eq_one : ∀ s > 0, ∀ x : SpaceTime,
      ∫ y : SpaceTime, heatKernelPositionSpace s ‖timeReflection x - y‖ = 1 :=
    fun s hs x => heatKernelPositionSpace_integral_translated s hs (timeReflection x)
  have hCf_nonneg : 0 ≤ Cf := by
    have := hCf 0
    linarith [norm_nonneg (f 0)]
  exact schwinger_bound_integrable_fubini m f Cf hCf h_f_int hCf_nonneg h_y_eq_one h_exp_int


/-- Proves that s⁻² * exp(-a/s) is integrable on (0, ∞) by substituting z = 1/s.

The key insight is that with f(s) = s⁻¹:
- f '' (0,∞) = (0,∞)
- f is antitone on (0,∞)
- f'(s) = -s⁻², so -f'(s) = s⁻²
- Under substitution z = 1/s: s⁻² * exp(-a/s) ds becomes exp(-a·z) dz
- ∫₀^∞ exp(-a·z) dz is finite for a > 0

This uses `integrableOn_image_iff_integrableOn_deriv_smul_of_antitoneOn`.
-/
theorem integrable_s_inv_sq_exp_neg_inv_s {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun s => s^((-2 : ℝ)) * Real.exp (-a / s)) (Set.Ioi 0) := by
  -- Strategy: Use the change of variables theorem
  -- IntegrableOn g (f '' s) ↔ IntegrableOn (fun x ↦ (-f' x) • g (f x)) s
  -- With f(s) = s⁻¹, f'(s) = -s⁻², we have -f'(s) = s⁻²
  -- With g(z) = exp(-a*z), we have g(f(s)) = exp(-a/s)
  -- So RHS is IntegrableOn (s ↦ s⁻² * exp(-a/s)) (Ioi 0) ← what we want!
  -- And f '' (Ioi 0) = Ioi 0, so LHS is IntegrableOn (z ↦ exp(-a*z)) (Ioi 0) ← known!
  -- Step 1: The exp integral is integrable
  have h_exp_int : IntegrableOn (fun z => Real.exp (-a * z)) (Set.Ioi 0) :=
    integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) 0
  -- Step 2: f '' (Ioi 0) = Ioi 0
  have h_img : (fun s : ℝ => s⁻¹) '' Set.Ioi 0 = Set.Ioi 0 := by
    ext y; simp only [Set.mem_image, Set.mem_Ioi]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact inv_pos.mpr hx
    · intro hy; use y⁻¹; exact ⟨inv_pos.mpr hy, inv_inv y⟩
  -- Step 3: Define f' and apply the iff
  let f' : ℝ → ℝ := fun s => -(s^((-2 : ℝ)))
  have h_iff := integrableOn_image_iff_integrableOn_deriv_smul_of_antitoneOn
    (f := fun s => s⁻¹) (f' := f') (s := Set.Ioi 0) (g := fun z => Real.exp (-a * z))
    measurableSet_Ioi
    (fun s hs => by
      simp only [f']
      have hs_pos : 0 < s := Set.mem_Ioi.mp hs
      have hs_ne : s ≠ 0 := ne_of_gt hs_pos
      have h : HasDerivAt (fun x => x⁻¹) (-(s^((-2 : ℝ)))) s := by
        have hderiv := hasDerivAt_inv hs_ne
        -- hasDerivAt_inv gives deriv = -(s^2)⁻¹ where exponent is ℕ
        -- We need -(s^(-2 : ℝ)) which equals -(s^2)⁻¹
        have heq : -(s^((-2 : ℝ))) = -(s ^ (2 : ℕ))⁻¹ := by
          rw [Real.rpow_neg (le_of_lt hs_pos)]
          congr 2
          exact Real.rpow_natCast s 2
        rwa [heq]
      exact h.hasDerivWithinAt)
    (fun x hx y _ hxy => inv_anti₀ hx hxy)
  -- Step 4: Rewrite using h_img and apply the iff
  rw [h_img] at h_iff
  -- Step 5: h_exp_int gives LHS, we need RHS which matches our goal (up to simp)
  have h_target := h_iff.mp h_exp_int
  -- Step 6: Show h_target matches the goal
  refine h_target.congr_fun ?_ measurableSet_Ioi
  intro s hs
  simp only [f', neg_neg, smul_eq_mul]
  -- Goal: s^(-2) * exp(-a * s⁻¹) = s^(-2) * exp(-a/s)
  -- These are equal since s⁻¹ = 1/s and -a * (1/s) = -a/s
  rfl

/-- Dominating function for the Fubini swap in `fubini_s_ksp_swap`.

    Represents the bound `C * s^(3/2) * exp(-s(m² + k²))` which comes from:
    1. Linear vanishing of f at t=0 giving s^(3/2) scaling (offsetting s^(-2) divergence).
    2. Exponential decay in mass and momentum.
-/
def dominateG (C : ℝ) (m : ℝ) (p : ℝ × SpatialCoords) : ℝ :=
  if p.1 > 0 then
    C * p.1 ^ (3 / 2 : ℝ) * Real.exp (-p.1 * (‖p.2‖^2 + m^2))
  else 0

/-- Theoretically proven integrability of `dominateG`.

    Integrable on (0, ∞) × ℝ³ because:
    ∫ exp(-s|k|²) dk = (π/s)^(3/2).
    ∫ s^(3/2) * (π/s)^(3/2) * exp(-s*m²) ds = π^(3/2) ∫ exp(-s*m²) ds.
    The latter converges for m > 0.
-/
theorem integrable_dominate_G (C : ℝ) (m : ℝ) [Fact (0 < m)] :
    Integrable (dominateG C m) ((volume.restrict (Set.Ioi 0)).prod volume) := by
  have hm : 0 < m := Fact.out
  let μ : Measure (ℝ × SpatialCoords) := (volume.restrict (Set.Ioi 0)).prod volume
  -- Core function G₀(s,k) = s^(3/2) * exp(-s(|k|² + m²)) for s > 0, else 0
  let G₀ : ℝ × SpatialCoords → ℝ := fun p =>
    if p.1 > 0 then p.1 ^ (3/2 : ℝ) * Real.exp (-p.1 * (‖p.2‖^2 + m^2)) else 0
  -- dominateG = C * G₀
  have hG_eq : dominateG C m = fun p => C * G₀ p := by
    ext p
    simp only [dominateG, G₀]
    split_ifs with hp <;> ring
  rw [hG_eq]
  -- G₀ is measurable
  have hG₀_meas : Measurable G₀ := by
    apply Measurable.ite
    · exact measurableSet_lt measurable_const measurable_fst
    · apply Measurable.mul
      · exact (measurable_fst.pow_const _)
      · exact (measurable_fst.neg.mul
          ((measurable_snd.norm.pow_const 2).add measurable_const)).exp
    · exact measurable_const
  -- G₀ is nonnegative
  have hG₀_nn : ∀ p : ℝ × SpatialCoords, 0 ≤ G₀ p := by
    intro p
    simp only [G₀]
    split_ifs with hp
    · apply mul_nonneg
      · exact Real.rpow_nonneg (le_of_lt hp) _
      · exact Real.exp_nonneg _
    · exact le_refl 0
  -- It suffices to show G₀ is integrable (then const_mul gives C * G₀)
  suffices hG₀_int : Integrable G₀ μ by
    exact hG₀_int.const_mul C
  -- Key: the lintegral of G₀ is finite
  -- ∫∫ G₀(s,k) dk ds = ∫_s ∫_k s^(3/2) exp(-s(|k|² + m²)) dk ds
  --                  = ∫_s s^(3/2) exp(-sm²) * (π/s)^(3/2) ds
  --                  = π^(3/2) ∫_s exp(-sm²) ds = π^(3/2) / m²
  have h_lintegral_finite : ∫⁻ p : ℝ × SpatialCoords, ENNReal.ofReal (G₀ p) ∂μ < ⊤ := by
    -- Use Tonelli to factor the lintegral
    have hG₀_ae_meas : AEMeasurable G₀ μ := hG₀_meas.aemeasurable
    have h_eq : ∫⁻ p : ℝ × SpatialCoords, ENNReal.ofReal (G₀ p) ∂μ =
        ∫⁻ s in Set.Ioi (0 : ℝ), ∫⁻ k : SpatialCoords,
          ENNReal.ofReal (G₀ (s, k)) ∂volume ∂volume := by
      simp only [μ]
      rw [MeasureTheory.lintegral_prod _ (hG₀_meas.ennreal_ofReal.aemeasurable)]
    rw [h_eq]
    -- Strategy: Bound the inner integral, then show outer integral is finite
    -- G₀(s,k) = s^(3/2) * exp(-sm²) * exp(-s|k|²) for s > 0, k ∈ ℝ³
    -- The inner integral ∫_k s^(3/2) exp(-sm²) exp(-s|k|²) dk
    -- = s^(3/2) * exp(-sm²) * (π/s)^(3/2)  [Gaussian integral]
    -- = π^(3/2) * exp(-sm²)
    -- Bound: for s ∈ Ioi 0, G₀(s,k) ≤ s^(3/2) * exp(-s*|k|²)
    -- (since exp(-sm²) ≤ 1)
    -- Key helper: s^(3/2) * (π/s)^(3/2) = π^(3/2) is a finite constant
    -- The outer integral ∫_0^∞ π^(3/2) * exp(-sm²) ds = π^(3/2) / m² < ∞
    -- Use monotonicity and bound by a computable integral
    -- First show the equality of integrands on Ioi 0
    have h_eq_integrand : ∀ᵐ s ∂(volume.restrict (Set.Ioi 0)), ∀ k : SpatialCoords,
        G₀ (s, k) = s ^ (3/2 : ℝ) * Real.exp (-s * m^2) * Real.exp (-s * ‖k‖^2) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs k
      have hs_pos : s > 0 := hs
      simp only [G₀, hs_pos, ↓reduceIte]
      -- G₀(s,k) = s^(3/2) * exp(-s(|k|² + m²)) = s^(3/2) * exp(-sm²) * exp(-s|k|²)
      -- Split: exp(-s(|k|² + m²)) = exp(-s*|k|² + (-s*m²)) = exp(-s*|k|²) * exp(-s*m²)
      have h_exp_split : Real.exp (-s * (‖k‖^2 + m^2)) =
          Real.exp (-s * ‖k‖^2) * Real.exp (-s * m^2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [h_exp_split]
      ring
    calc ∫⁻ s in Set.Ioi (0 : ℝ), ∫⁻ k : SpatialCoords,
          ENNReal.ofReal (G₀ (s, k)) ∂volume ∂volume
        = ∫⁻ s in Set.Ioi (0 : ℝ), ∫⁻ k : SpatialCoords,
            ENNReal.ofReal (s ^ (3/2 : ℝ) * Real.exp (-s * m^2) *
              Real.exp (-s * ‖k‖^2)) ∂volume ∂volume := by
          apply lintegral_congr_ae
          filter_upwards [h_eq_integrand] with s hs
          congr 1
          ext k
          rw [hs k]
      _ < ⊤ := by
          -- Strategy: Compute exact inner integral using Gaussian formula, then bound outer
          --
          -- For s > 0, the integrand factors as:
          -- s^(3/2) * exp(-sm²) * exp(-s|k|²)
          --
          -- Inner k-integral: ∫_k exp(-s|k|²) dk = (π/s)^(3/2)  [Gaussian integral]
          -- So s^(3/2) * (π/s)^(3/2) = π^(3/2), giving inner = π^(3/2) * exp(-sm²)
          --
          -- Outer s-integral: ∫_0^∞ π^(3/2) * exp(-sm²) ds = π^(3/2) / m² < ∞
          -- First show inner integral equality
          have h_inner : ∀ s ∈ Set.Ioi (0 : ℝ),
              ∫⁻ k : SpatialCoords, ENNReal.ofReal (s ^ (3/2 : ℝ) * Real.exp (-s * m^2) *
                Real.exp (-s * ‖k‖^2)) = ENNReal.ofReal (π ^ (3/2 : ℝ) * Real.exp (-s * m^2)) := by
            intro s hs
            have hs_pos : 0 < s := hs
            -- The Gaussian exp(-s|k|²) is integrable for s > 0
            -- (Inline proof since gaussian_integrable_spatialCoords is defined later)
            have h_gauss_int : Integrable (fun k_sp : SpatialCoords => Real.exp (-s * ‖k_sp‖^2)) :=
              by
              have hs' : 0 < (s : ℂ).re := by simp [hs_pos]
              have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := SpatialCoords)
                hs' 0 0
              simp only [zero_mul, add_zero, inner_zero_left, Complex.ofReal_zero] at h
              have h_eq : (fun k_sp : SpatialCoords => Complex.exp (-(s : ℂ) * ‖k_sp‖^2)) =
                  (fun k_sp => (Real.exp (-s * ‖k_sp‖^2) : ℂ)) := by
                ext k_sp
                simp only [Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul,
                  Complex.ofReal_pow]
              rw [h_eq] at h
              exact h.re
            -- Show integrand is nonnegative
            have h_integrand_nn : ∀ k : SpatialCoords,
                0 ≤ s ^ (3/2 : ℝ) * Real.exp (-s * m^2) * Real.exp (-s * ‖k‖^2) := by
              intro k
              positivity
            -- Show integrand is integrable
            have h_integrand_int : Integrable
                (fun k : SpatialCoords => s ^ (3/2 : ℝ) * Real.exp (-s * m^2) * Real.exp (-s *
                   ‖k‖^2)) :=
              h_gauss_int.const_mul _
            -- Convert lintegral to integral using ofReal_integral_eq_lintegral_ofReal
            rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_integrand_int
                (ae_of_all _ h_integrand_nn)]
            -- Pull out constant
            have h_factor : (fun k : SpatialCoords => s ^ (3/2 : ℝ) * Real.exp (-s * m^2) *
                Real.exp (-s * ‖k‖^2)) = fun k => (s ^ (3/2 : ℝ) * Real.exp (-s * m^2)) *
                Real.exp (-s * ‖k‖^2) := by ext k; ring
            rw [h_factor, MeasureTheory.integral_const_mul]
            -- Use Gaussian formula: ∫ exp(-s|k|²) dk = (π/s)^(3/2)
            have h_dim : Module.finrank ℝ SpatialCoords = 3 := by simp [SpatialCoords]
            have h_gauss_val := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := SpatialCoords)
              hs_pos
            rw [h_dim] at h_gauss_val
            rw [h_gauss_val]
            -- Now: s^(3/2) * exp(-sm²) * (π/s)^(3/2) = π^(3/2) * exp(-sm²)
            congr 1
            -- Goal: s^(3/2) * exp(-sm²) * (π/s)^(3/2) = π^(3/2) * exp(-sm²)
            have hs_ne : s ≠ 0 := ne_of_gt hs_pos
            have h_s_pos' : 0 < s ^ (3/2 : ℝ) := Real.rpow_pos_of_pos hs_pos _
            have h_pi_pos : 0 < π ^ (3/2 : ℝ) := Real.rpow_pos_of_pos Real.pi_pos _
            -- (π/s)^(3/2) = π^(3/2) / s^(3/2) for s > 0
            -- Note: the exponent in Gaussian formula comes as ↑3/2 = (3:ℕ)/2 : ℝ
            have h_exp_eq : (↑3 : ℝ) / 2 = (3/2 : ℝ) := by norm_num
            rw [h_exp_eq]
            rw [Real.div_rpow (le_of_lt Real.pi_pos) (le_of_lt hs_pos)]
            -- s^(3/2) * exp(-sm²) * (π^(3/2) / s^(3/2)) = π^(3/2) * exp(-sm²)
            have h_s_ne' : s ^ (3/2 : ℝ) ≠ 0 := ne_of_gt h_s_pos'
            field_simp [h_s_ne']
            -- After field_simp, goal should be s^(3/2) * exp * π^(3/2) = π^(3/2) * exp * s^(3/2)
            ring_nf
          -- Outer integral: use the inner equality to simplify
          -- We need: ∫⁻ s ∈ Ioi 0, (LHS inner) = ∫⁻ s ∈ Ioi 0, (RHS inner)
          have h_eqon : Set.EqOn
              (fun s => ∫⁻ k : SpatialCoords,
                ENNReal.ofReal (s ^ (3/2 : ℝ) * Real.exp (-s * m^2) * Real.exp (-s * ‖k‖^2)))
              (fun s => ENNReal.ofReal (π ^ (3/2 : ℝ) * Real.exp (-s * m^2)))
              (Set.Ioi 0) := by
            intro s hs
            exact h_inner s hs
          have h_lintegral_eq : ∫⁻ s in Set.Ioi (0 : ℝ), ∫⁻ k : SpatialCoords,
                ENNReal.ofReal (s ^ (3/2 : ℝ) * Real.exp (-s * m^2) *
                  Real.exp (-s * ‖k‖^2)) ∂volume ∂volume =
              ∫⁻ s in Set.Ioi (0 : ℝ),
                ENNReal.ofReal (π ^ (3/2 : ℝ) * Real.exp (-s * m^2)) ∂volume := by
            exact MeasureTheory.setLIntegral_congr_fun measurableSet_Ioi h_eqon
          calc ∫⁻ s in Set.Ioi (0 : ℝ), ∫⁻ k : SpatialCoords,
                ENNReal.ofReal (s ^ (3/2 : ℝ) * Real.exp (-s * m^2) *
                  Real.exp (-s * ‖k‖^2)) ∂volume ∂volume
            = ∫⁻ s in Set.Ioi (0 : ℝ),
                ENNReal.ofReal (π ^ (3/2 : ℝ) * Real.exp (-s * m^2)) ∂volume := h_lintegral_eq
            _ < ⊤ := by
              -- The integrand is nonnegative and integrable
              have h_exp_int : IntegrableOn (fun s => Real.exp (-s * m^2)) (Set.Ioi 0) :=
                integrableOn_exp_neg_mul_sq_Ioi m hm
              have h_prod_int : IntegrableOn (fun s => π ^ (3/2 : ℝ) * Real.exp (-s * m^2))
                (Set.Ioi 0) :=
                h_exp_int.const_mul _
              exact h_prod_int.setLIntegral_lt_top
  refine ⟨hG₀_meas.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  calc ∫⁻ p, ‖G₀ p‖₊ ∂μ
      = ∫⁻ p, ENNReal.ofReal (G₀ p) ∂μ := by
          congr 1
          ext p
          -- ‖G₀ p‖₊ = (G₀ p).toNNReal since G₀ p ≥ 0
          -- and ENNReal.ofReal (G₀ p) = (G₀ p).toNNReal
          have h_nn := hG₀_nn p
          simp only [Real.nnnorm_of_nonneg h_nn, ENNReal.ofReal_eq_coe_nnreal h_nn]
    _ < ⊤ := h_lintegral_finite

/-- spatialPart is continuous (projection followed by continuous linear equiv). -/
lemma continuous_spatialPart : Continuous spatialPart := by
  unfold spatialPart
  apply (EuclideanSpace.equiv (Fin (STDimension - 1)) ℝ).symm.continuous.comp
  apply continuous_pi
  intro i
  have h : i.val + 1 < STDimension := by simp [STDimension]; omega
  exact PiLp.continuous_apply 2 (fun _ : Fin STDimension => ℝ) (⟨i.val + 1, h⟩ : Fin STDimension)

/-- `spatialPart` is measurable. -/
lemma spatialPart_measurable : Measurable (spatialPart : SpaceTime → SpatialCoords) :=
  continuous_spatialPart.measurable

/-- The integrand for `fubini_s_ksp_swap` is strongly measurable.

    The integrand is:
    `((s, k_sp), x, y) ↦ fbar(x) · f(y) · √(π/s) · exp(...) · exp(...) · exp(...)`

    After two applications of `StronglyMeasurable.integral_prod_right`, the type is:
    `(((ℝ × SpatialCoords) × SpaceTime) × SpaceTime) → ℂ`
    represented as `x : (ℝ × SpatialCoords) × SpaceTime`, `y : SpaceTime`.

    This is a product of continuous/measurable functions, hence measurable.
-/
lemma fubini_s_ksp_integrand_stronglyMeasurable (m : ℝ) (f : TestFunctionℂ) :
    StronglyMeasurable (Function.uncurry fun (x : (ℝ × SpatialCoords) × SpaceTime) (y : SpaceTime)
      =>
      (starRingEnd ℂ (f x.2)) * f y *
        (Real.sqrt (π / x.1.1) : ℂ) * Complex.exp (-((-(x.2.ofLp 0) - y.ofLp 0)^2 / (4 * x.1.1) :
           ℝ)) *
        Complex.exp (-(x.1.1 : ℂ) * (‖x.1.2‖^2 + m^2)) *
        Complex.exp (-Complex.I * spatialDot x.1.2 (spatialPart x.2 - spatialPart y))) := by
  apply Measurable.stronglyMeasurable
  have hf : Measurable f := f.continuous.measurable
  have hsp : Measurable (spatialPart : SpaceTime → SpatialCoords) := spatialPart_measurable
  simp only [spatialDot_eq_inner]
  fun_prop (disch := assumption)

/-! ### Heat Kernel Moment Bounds

The key technical result for `hF_le_G` is computing the Gaussian moment integral:

  ∫∫_{x₀,y₀>0} x₀ · y₀ · √(π/s) · exp(-(x₀+y₀)²/(4s)) dx₀ dy₀ = (4/3)√π · s^{3/2}

This is done via change of variables u = x₀ + y₀, v = x₀ - y₀ and standard Gaussian integrals.
-/

/-- The 1D Gaussian integral ∫₀^∞ u³ exp(-u²/(4s)) du = 8s² for s > 0.

    This follows from the general formula ∫₀^∞ u^n exp(-au²) du using Gamma functions.

    **Proof:**
    Using `integral_rpow_mul_exp_neg_mul_rpow` with p=2, q=3, b=1/(4s):
    - ∫ u³ exp(-b·u²) du = b^(-(3+1)/2) * (1/2) * Γ((3+1)/2)
    - = b^(-2) * (1/2) * Γ(2)
    - = (4s)² * (1/2) * 1   [since Γ(2) = 1]
    - = 8s²
-/
lemma integral_u_cubed_gaussian (s : ℝ) (hs : 0 < s) :
    ∫ u in Set.Ioi 0, u^3 * Real.exp (-u^2 / (4 * s)) = 8 * s^2 := by
  have hb : 0 < 1 / (4 * s) := by positivity
  -- Rewrite to use rpow throughout
  have h_integrand_eq : ∀ u : ℝ, u^3 * Real.exp (-u^2 / (4 * s)) =
                                 u ^ (3:ℝ) * Real.exp (-(1/(4*s)) * u^(2:ℝ)) := by
    intro u
    rw [show u^3 = u ^ (3:ℝ) from (Real.rpow_natCast u 3).symm]
    rw [show u^2 = u ^ (2:ℝ) from (Real.rpow_natCast u 2).symm]
    congr 2
    field_simp
  simp_rw [h_integrand_eq]
  -- Apply the standard Gaussian integral formula
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 3) (b := 1/(4*s))
    (by norm_num : (0:ℝ) < 2) (by norm_num : (-1:ℝ) < 3) hb
  -- Gamma(2) = 1
  have hG2 : Real.Gamma 2 = 1 := Real.Gamma_two
  -- Now the LHS matches the formula in h
  calc ∫ u in Set.Ioi 0, u ^ (3:ℝ) * Real.exp (-(1 / (4 * s)) * u ^ (2:ℝ))
      = (1 / (4 * s)) ^ (-(3 + 1) / 2) * (1 / 2) * Real.Gamma ((3 + 1) / 2) := h
    _ = (1 / (4 * s)) ^ ((-2) : ℝ) * (1 / 2) * Real.Gamma 2 := by
        congr 2 <;> norm_num
    _ = (1 / (4 * s)) ^ ((-2) : ℝ) * (1 / 2) * 1 := by rw [hG2]
    _ = (4 * s) ^ (2 : ℝ) * (1 / 2) := by
        rw [Real.rpow_neg (le_of_lt hb), Real.rpow_two, Real.rpow_two]
        field_simp
    _ = 16 * s^2 * (1 / 2) := by rw [Real.rpow_two]; ring
    _ = 8 * s^2 := by ring

/-- **Triangular Fubini identity for the quadrant-to-triangle change of variables**

    For non-negative integrable f, the change of variables u = x + y transforms
    the integral over the first quadrant {(x,y) : x > 0, y > 0} to an integral
    over the triangular region {(x,u) : u > 0, 0 < x < u}:

    ∫_{x>0} ∫_{y>0} f(x, x+y) dy dx = ∫_{u>0} ∫_{0<x<u} f(x, u) dx du

    This is a standard result from Fubini-Tonelli theorem. The Jacobian of the
    map (x, y) ↦ (x, u) where u = x + y has determinant 1.

    **Proof sketch:**
    1. Both regions have the same measure under the product Lebesgue measure
    2. The map (x, y) ↦ (x, x+y) is measure-preserving (shear with det = 1)
    3. Apply Fubini to swap the order of integration
-/
lemma triangular_fubini_quadrant {f : ℝ → ℝ → ℝ}
    (_hf_nn : ∀ x y, 0 ≤ x → 0 ≤ y → 0 ≤ f x (x + y))
    (hf_int : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      Set.indicator (Set.Ioi 0 ×ˢ Set.Ioi 0) (fun q => f q.1 (q.1 + q.2)) p) volume) :
    ∫ x in Set.Ioi 0, ∫ y in Set.Ioi 0, f x (x + y) =
    ∫ u in Set.Ioi 0, ∫ x in Set.Ioo 0 u, f x u := by
  -- The triangular Fubini identity follows from the change of variables (x, y) ↦ (x, u)
  -- where u = x + y. The shear map has Jacobian 1.
  --
  -- LHS: ∫_{x>0} ∫_{y>0} f(x, x+y) dy dx
  -- RHS: ∫_{u>0} ∫_{0<x<u} f(x, u) dx du
  --
  -- These are equal because:
  -- - When x > 0 and y > 0, we have u = x + y > x > 0
  -- - The map (x, y) ↦ (x, x + y) has Jacobian 1
  -- - The inverse map (x, u) ↦ (x, u - x) also has Jacobian 1
  --
  -- This is a standard result; we use a direct reindexing argument via Tonelli/Fubini.
  -- Step 1: For fixed x > 0, the inner integral ∫_{y>0} f(x, x+y) dy equals
  --         ∫_{u>x} f(x, u) du via the substitution u = x + y
  have h_inner : ∀ x : ℝ, 0 < x →
      ∫ y in Set.Ioi 0, f x (x + y) = ∫ u in Set.Ioi x, f x u := by
    intro x hx
    -- Change of variables: u = x + y, so y = u - x, dy = du
    -- When y ∈ (0, ∞), u ∈ (x, ∞)
    -- Use the change of variables formula with φ(y) = y + x
    -- The image of Ioi 0 under (· + x) is Ioi x
    have h_image : (fun y => y + x) '' Set.Ioi 0 = Set.Ioi x := by
      ext u
      simp only [Set.mem_image, Set.mem_Ioi]
      constructor
      · rintro ⟨y, hy, rfl⟩; linarith
      · intro hu; use u - x; constructor <;> linarith
    -- Apply integral_image_eq_integral_abs_deriv_smul with derivative = 1
    rw [← h_image]
    symm
    rw [MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
        (f' := fun _ => (1 : ℝ))]
    · -- The Jacobian |d(y+x)/dy| = |1| = 1, so the integral is just ∫ f x (y + x)
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro y _
      simp only [smul_eq_mul, abs_one, one_mul]
      -- f x (y + x) = f x (x + y)
      congr 1; ring
    · -- Derivative condition: HasDerivWithinAt (· + x) 1 (Ioi 0) y
      intro y _
      exact (hasDerivWithinAt_id y _).add_const x
    · -- Injectivity of (· + x)
      exact fun _ _ _ _ h => by linarith
  -- Step 2: ∫_{x>0} ∫_{u>x} f(x, u) du dx = ∫_{u>0} ∫_{0<x<u} f(x, u) dx du
  -- This is a standard Tonelli/Fubini reindexing for the region {(x, u) : 0 < x < u}
  have h_reindex : ∫ x in Set.Ioi 0, ∫ u in Set.Ioi x, f x u =
      ∫ u in Set.Ioi 0, ∫ x in Set.Ioo 0 u, f x u := by
    -- Both integrals cover the same triangular region T = {(x, u) : 0 < x < u}.
    let T : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < p.2}
    let g : ℝ × ℝ → ℝ := T.indicator (fun p => f p.1 p.2)
    -- Proven using Fubini on ℝ² for g
    -- 1. Show g is integrable using the shear map and hf_int
    have h_g_int : Integrable g (volume.prod volume) := by
      let φ : ℝ × ℝ → ℝ × ℝ := fun p => (p.1, p.1 + p.2)
      let φ_homeo : Homeomorph (ℝ × ℝ) (ℝ × ℝ) := {
        toFun := φ
        invFun := fun p => (p.1, p.2 - p.1)
        left_inv := fun _ => by simp [φ]
        right_inv := fun _ => by simp [φ]
        continuous_toFun := by continuity
        continuous_invFun := by continuity
      }
      -- φ is measure preserving
      -- φ(x, y) = (x, x + y) is measure preserving on ℝ² with Lebesgue measure
      -- This follows from: measurePreserving_add_prod gives (x, y) ↦ (x + y, y) is
      -- measure-preserving
      -- And composing with swaps: φ = swap ∘ (add_prod) ∘ swap
      have hφ_mp : MeasurePreserving φ (volume.prod volume) (volume.prod volume) := by
        -- swap: (a, b) ↦ (b, a)
        -- add_prod: (a, b) ↦ (a + b, b)
        -- We want: (x, y) ↦ (x, x + y)
        -- = (x, y) ↦ swap (y, x) ↦ swap (add_prod (y, x)) = swap (y + x, x) = (x, y + x) = (x, x +
        -- y)
        have h_swap : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ)
            ((volume : Measure ℝ).prod volume) (volume.prod volume) :=
          MeasureTheory.Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := volume)
        have h_add : MeasurePreserving (fun z : ℝ × ℝ => (z.1 + z.2, z.2))
            ((volume : Measure ℝ).prod volume) (volume.prod volume) :=
          MeasureTheory.measurePreserving_add_prod (volume : Measure ℝ) volume
        -- φ = swap ∘ add_prod ∘ swap
        have h_eq : φ = Prod.swap ∘ (fun z : ℝ × ℝ => (z.1 + z.2, z.2)) ∘ Prod.swap := by
          ext ⟨x, y⟩
          · simp only [φ, Prod.swap, Function.comp_apply]
          · simp only [φ, Prod.swap, Function.comp_apply]; ring
        rw [h_eq]
        exact h_swap.comp (h_add.comp h_swap)
      -- g ∘ φ = indicator of square
      have h_eq : g ∘ φ = (Set.Ioi 0 ×ˢ Set.Ioi 0).indicator (fun q => f q.1 (q.1 + q.2)) := by
        ext ⟨x, y⟩
        simp only [g, T, φ, Set.indicator_apply, Set.mem_prod, Set.mem_Ioi, Set.mem_setOf_eq,
          Function.comp_apply]
        split_ifs <;> simp_all
      -- Apply transfer
      rw [← hφ_mp.integrable_comp_emb φ_homeo.measurableEmbedding]
      rw [h_eq]
      exact hf_int
    -- 2. LHS = ∫∫ g
    have h_lhs : ∫ x in Set.Ioi 0, ∫ u in Set.Ioi x, f x u = ∫ x, ∫ u, g (x, u) := by
      rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      simp only [g, T, Set.indicator_apply, Set.mem_Ioi]
      split_ifs with hx
      · rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
        apply MeasureTheory.integral_congr_ae
        filter_upwards with u
        simp [Set.indicator_apply, Set.mem_Ioi, hx]
      · simp [hx]
    -- 3. RHS = ∫∫ g (swapped)
    have h_rhs : ∫ u in Set.Ioi 0, ∫ x in Set.Ioo 0 u, f x u = ∫ u, ∫ x, g (x, u) := by
      rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with u
      simp only [Set.indicator_apply, Set.mem_Ioi]
      split_ifs with hu
      · rw [← MeasureTheory.integral_indicator measurableSet_Ioo]
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        -- Goal: (Set.Ioo 0 u).indicator (fun x ↦ f x u) x = g (x, u)
        -- g (x, u) = T.indicator (fun p ↦ f p.1 p.2) (x, u)
        -- T = {p | 0 < p.1 ∧ p.1 < p.2}, so (x, u) ∈ T iff 0 < x ∧ x < u
        -- Set.Ioo 0 u = {x | 0 < x ∧ x < u}
        -- These are the same condition!
        simp only [g, T, Set.indicator_apply, Set.mem_Ioo, Set.mem_setOf_eq]
      · symm
        apply MeasureTheory.integral_eq_zero_of_ae
        filter_upwards with x
        simp only [g, T, Set.indicator_apply, Set.mem_setOf_eq]
        split_ifs with hcond
        · exfalso; exact hu (lt_trans hcond.1 hcond.2)
        · rfl
    -- 4. Apply Fubini
    -- 4. Apply Fubini
    rw [h_lhs, h_rhs]
    exact MeasureTheory.integral_integral_swap h_g_int
  -- Combine steps
  calc ∫ x in Set.Ioi 0, ∫ y in Set.Ioi 0, f x (x + y)
      = ∫ x in Set.Ioi 0, ∫ u in Set.Ioi x, f x u := by
          apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
          intro x hx
          exact h_inner x hx
    _ = ∫ u in Set.Ioi 0, ∫ x in Set.Ioo 0 u, f x u := h_reindex

/-- The double Gaussian moment integral:
    ∫∫_{x₀,y₀>0} x₀·y₀·√(π/s)·exp(-(x₀+y₀)²/(4s)) dx₀ dy₀ = (4/3)√π · s^{3/2}

    This is the key bound relating linear vanishing of f at t=0 to the s^{3/2} scaling in
    dominateG.

    **Proof** (following user's verification):
    Let J be the integral. Change variables: u = x₀ + y₀.
    For fixed u, x₀ ranges from 0 to u, and y₀ = u - x₀. Jacobian = 1.

    J = √(π/s) ∫₀^∞ exp(-u²/(4s)) [∫₀ᵘ x₀(u - x₀) dx₀] du

    Inner integral: ∫₀ᵘ (ux₀ - x₀²) dx₀ = [ux₀²/2 - x₀³/3]₀ᵘ = u³/2 - u³/3 = u³/6

    So: J = √(π/s) · (1/6) · ∫₀^∞ u³ exp(-u²/(4s)) du
          = √(π/s) · (1/6) · 8s²  [by integral_u_cubed_gaussian]
          = √π · s^(-1/2) · (4/3) · s²
          = (4/3)√π · s^(3/2)
-/
lemma heat_kernel_moment_integral (s : ℝ) (hs : 0 < s) :
    ∫ x₀ in Set.Ioi 0, ∫ y₀ in Set.Ioi 0,
      x₀ * y₀ * Real.sqrt (π / s) * Real.exp (-(x₀ + y₀)^2 / (4 * s)) =
    (4/3) * Real.sqrt π * s^(3/2 : ℝ) := by
  -- Step 1: Get the key integral ∫₀^∞ u³ exp(-u²/(4s)) du = 8s²
  have h_u_int := integral_u_cubed_gaussian s hs
  -- Step 2: The algebraic identity: √(π/s) · (1/6) · 8s² = (4/3)√π · s^{3/2}
  have h_algebra : Real.sqrt (π / s) * (1/6) * (8 * s^2) = (4/3) * Real.sqrt π * s^(3/2 : ℝ) := by
    have hs' : (0 : ℝ) < s := hs
    have hs_ne : s ≠ 0 := ne_of_gt hs
    -- √(π/s) = √π / √s
    rw [Real.sqrt_div' π (le_of_lt hs)]
    -- s^{3/2} = s · √s
    have h32 : s^(3/2 : ℝ) = s * Real.sqrt s := by
      rw [show (3/2 : ℝ) = 1 + 1/2 by norm_num]
      rw [Real.rpow_add hs']
      simp only [Real.rpow_one]
      rw [Real.sqrt_eq_rpow]
    rw [h32]
    -- √s² = s (for s > 0)
    have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt (le_of_lt hs)
    have hsqrt_pos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
    have hsqrt_ne : Real.sqrt s ≠ 0 := ne_of_gt hsqrt_pos
    -- Goal: √π / √s * (1/6) * (8 * s²) = 4/3 * √π * (s * √s)
    calc Real.sqrt π / Real.sqrt s * (1 / 6) * (8 * s ^ 2)
        = Real.sqrt π * (8 * s^2) / (6 * Real.sqrt s) := by ring
      _ = Real.sqrt π * (4 * s^2) / (3 * Real.sqrt s) := by ring
      _ = 4 / 3 * Real.sqrt π * (s^2 / Real.sqrt s) := by ring
      _ = 4 / 3 * Real.sqrt π * (s * (s / Real.sqrt s)) := by ring
      _ = 4 / 3 * Real.sqrt π * (s * Real.sqrt s) := by
          congr 1
          congr 1
          -- s / √s = √s (since s = √s · √s)
          exact div_sqrt
  -- Step 3a: Pull out the constant √(π/s) from the integral
  have h_pull_const : ∫ x₀ in Set.Ioi 0, ∫ y₀ in Set.Ioi 0,
      x₀ * y₀ * Real.sqrt (π / s) * Real.exp (-(x₀ + y₀)^2 / (4 * s)) =
      Real.sqrt (π / s) * ∫ x₀ in Set.Ioi 0, ∫ y₀ in Set.Ioi 0,
        x₀ * y₀ * Real.exp (-(x₀ + y₀)^2 / (4 * s)) := by
    conv_lhs =>
      arg 2; ext x₀; arg 2; ext y₀
      rw [show x₀ * y₀ * Real.sqrt (π / s) * Real.exp (-(x₀ + y₀)^2 / (4 * s)) =
          Real.sqrt (π / s) * (x₀ * y₀ * Real.exp (-(x₀ + y₀)^2 / (4 * s))) by ring]
    simp_rw [MeasureTheory.integral_const_mul]
  -- Step 3b: The polynomial inner integral ∫₀ᵘ x(u-x) dx = u³/6
  have h_poly_int : ∀ u : ℝ, 0 < u →
      ∫ x in (0 : ℝ)..u, x * (u - x) = u^3 / 6 := by
    intro u hu
    have h1 : ∫ x in (0 : ℝ)..u, x * (u - x) = ∫ x in (0 : ℝ)..u, u * x - x^2 := by
      congr 1; ext x; ring
    rw [h1, intervalIntegral.integral_sub]
    · have hx : ∫ x in (0 : ℝ)..u, x = u^2 / 2 := by
        rw [show (fun x : ℝ => x) = (fun x => x^1) by ext; simp, integral_pow]
        simp; ring
      have hx2 : ∫ x in (0 : ℝ)..u, x^2 = u^3 / 3 := by
        rw [integral_pow]; simp; ring
      rw [intervalIntegral.integral_const_mul, hx, hx2]
      ring
    · exact (continuous_const.mul continuous_id).intervalIntegrable 0 u
    · exact (continuous_pow 2).intervalIntegrable 0 u
  -- Step 3c: The double integral via change of variables
  -- ∫∫_{x₀,y₀>0} x₀ y₀ exp(-(x₀+y₀)²/(4s)) = ∫_{u>0} exp(-u²/(4s)) · [∫₀ᵘ x₀(u-x₀) dx₀] du
  --                                         = ∫_{u>0} exp(-u²/(4s)) · (u³/6) du
  --                                         = (1/6) · 8s²
  have h_double_int : ∫ x₀ in Set.Ioi 0, ∫ y₀ in Set.Ioi 0,
      x₀ * y₀ * Real.exp (-(x₀ + y₀)^2 / (4 * s)) = (1/6) * (8 * s^2) := by
    -- The change of variables (x₀, y₀) ↦ (u, t) where u = x₀ + y₀, t = x₀
    -- transforms the first quadrant to the triangular region {(u,t) : u > 0, 0 < t < u}
    -- with Jacobian 1 (the inverse map (u,t) ↦ (t, u-t) has det = 1).
    --
    -- After change of variables:
    -- ∫_{u>0} [∫_{0<t<u} t(u-t) dt] exp(-u²/(4s)) du
    --   = ∫_{u>0} (u³/6) exp(-u²/(4s)) du   [by h_poly_int]
    --   = (1/6) ∫_{u>0} u³ exp(-u²/(4s)) du
    --   = (1/6) · 8s²                        [by h_u_int]
    calc ∫ x₀ in Set.Ioi 0, ∫ y₀ in Set.Ioi 0, x₀ * y₀ * Real.exp (-(x₀ + y₀)^2 / (4 * s))
        = ∫ u in Set.Ioi 0, Real.exp (-u^2 / (4 * s)) * (u^3 / 6) := by
          -- **Change of variables: First quadrant to triangular region**
          --
          -- The key identity is the "triangular Fubini" swap:
          -- ∫_{x>0} ∫_{y>0} f(x, x+y) dy dx = ∫_{u>0} ∫_{0<x<u} f(x, u) dx du
          --
          -- Here we have f(x, y) = x * y * exp(-(x+y)²/(4s)) and after the change
          -- u = x + y, the integrand becomes x * (u-x) * exp(-u²/(4s)).
          --
          -- Step 1: Apply triangular Fubini (change u = x₀ + y₀)
          -- Step 2: Factor out exp(-u²/(4s)) from inner integral
          -- Step 3: Compute inner integral ∫₀ᵘ x(u-x) dx = u³/6 using h_poly_int
          -- Apply the triangular Fubini identity via `triangular_fubini_quadrant`
          -- with g(x, u) = x * (u - x) * exp(-u²/(4s))
          have h_fubini : ∫ x₀ in Set.Ioi 0, ∫ y₀ in Set.Ioi 0,
              x₀ * y₀ * Real.exp (-(x₀ + y₀)^2 / (4 * s)) =
              ∫ u in Set.Ioi 0, ∫ x₀ in Set.Ioo 0 u,
                x₀ * (u - x₀) * Real.exp (-u^2 / (4 * s)) := by
            -- Rewrite LHS: x₀ * y₀ = x₀ * ((x₀ + y₀) - x₀) when we set u = x₀ + y₀
            -- This is exactly the triangular Fubini setup
            have h_integrand : ∀ x₀ y₀ : ℝ, x₀ * y₀ * Real.exp (-(x₀ + y₀)^2 / (4 * s)) =
                x₀ * ((x₀ + y₀) - x₀) * Real.exp (-(x₀ + y₀)^2 / (4 * s)) := by
              intro x₀ y₀; ring_nf
            simp_rw [h_integrand]
            -- Apply triangular_fubini_quadrant with g(x, u) = x * (u - x) * exp(-u²/(4s))
            -- The identity: ∫_{x>0} ∫_{y>0} g(x, x+y) dy = ∫_{u>0} ∫_{0<x<u} g(x, u) dx
            have hf_nn : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
                0 ≤ (fun x u => x * (u - x) * Real.exp (-u^2 / (4 * s))) x (x + y) := by
              intro x y hx hy
              simp only
              have h1 : x + y - x = y := by ring
              rw [h1]
              apply mul_nonneg
              · exact mul_nonneg hx hy
              · exact Real.exp_nonneg _
            convert triangular_fubini_quadrant
              (f := fun x u => x * (u - x) * Real.exp (-u^2 / (4 * s)))
              (_hf_nn := hf_nn)
              (hf_int := by
                -- Need to show: (x, y) ↦ x·y·exp(-(x+y)²/(4s)) is integrable over (0,∞)²
                -- Strategy: bound by |x|·exp(-x²/(4s)) · |y|·exp(-y²/(4s)) using
                -- (x+y)² ≥ x² + y² for x,y > 0, then use Integrable.mul_prod
                rw [MeasureTheory.integrable_indicator_iff (measurableSet_Ioi.prod
                  measurableSet_Ioi)]
                rw [MeasureTheory.IntegrableOn]
                -- Key bound: for x, y > 0, (x+y)² = x² + 2xy + y² > x² + y² since 2xy > 0
                -- So exp(-(x+y)²/(4s)) < exp(-(x²+y²)/(4s)) = exp(-x²/(4s))·exp(-y²/(4s))
                -- Thus x·y·exp(-(x+y)²/(4s)) ≤ |x|·exp(-x²/(4s)) · |y|·exp(-y²/(4s))
                have hb : 0 < 1 / (4 * s) := by positivity
                have h_int_factor : MeasureTheory.Integrable
                    (fun x => |x| * Real.exp (-(1/(4*s)) * x^2)) volume := by
                  have := integrable_mul_exp_neg_mul_sq hb
                  convert this.norm using 1
                  ext x; rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
                -- Product integrability on full space dominates restricted
                have h_prod := MeasureTheory.Integrable.mul_prod h_int_factor h_int_factor
                -- h_prod is Integrable (on volume.prod volume), goal needs μ.restrict on product
                -- Since volume on ℝ × ℝ is volume.prod volume, h_prod.restrict gives integrability
                -- on restricted measure, then use Integrable.mono with pointwise bound
                have h_prod_restr : MeasureTheory.Integrable
                    (fun z : ℝ × ℝ => |z.1| * Real.exp (-(1/(4*s)) * z.1^2) *
                                      (|z.2| * Real.exp (-(1/(4*s)) * z.2^2)))
                    (MeasureTheory.volume.restrict (Set.Ioi 0 ×ˢ Set.Ioi 0)) := by
                  rw [MeasureTheory.Measure.volume_eq_prod]
                  exact h_prod.restrict (s := Set.Ioi 0 ×ˢ Set.Ioi 0)
                apply MeasureTheory.Integrable.mono h_prod_restr
                · fun_prop
                · -- Pointwise bound on Ioi 0 × Ioi 0
                  filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Ioi.prod
                    measurableSet_Ioi)] with ⟨x, y⟩ hxy
                  simp only [Set.mem_prod, Set.mem_Ioi] at hxy
                  obtain ⟨hx, hy⟩ := hxy
                  simp only [norm_mul, Real.norm_eq_abs]
                  -- Simplify abs values using x > 0, y > 0, exp > 0
                  rw [abs_of_pos hx, abs_of_pos hy, abs_of_pos (Real.exp_pos _),
                      abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
                  -- Now need to rewrite x + y - x to y
                  have h_simp : x + y - x = y := by ring
                  rw [h_simp, abs_of_pos hy]
                  -- Goal: x * y * exp(-(x+y)²/(4s)) ≤ x * exp(-x²/(4s)) * (y * exp(-y²/(4s)))
                  have h_exp_bound : Real.exp (-(x + y) ^ 2 / (4 * s)) ≤
                      Real.exp (-x^2 / (4 * s)) * Real.exp (-y^2 / (4 * s)) := by
                    rw [← Real.exp_add]
                    apply Real.exp_le_exp.mpr
                    have hxy_pos : 0 < x * y := mul_pos hx hy
                    -- Need: -(x+y)²/(4s) ≤ -x²/(4s) - y²/(4s)
                    -- i.e., -(x+y)²/(4s) ≤ -(x² + y²)/(4s)
                    -- i.e., (x+y)² ≥ x² + y² (dividing by -1/(4s) reverses)
                    -- (x+y)² = x² + 2xy + y² ≥ x² + y² since xy > 0
                    have h1 : -(x + y)^2 / (4 * s) ≤ -(x^2 + y^2) / (4 * s) := by
                      apply div_le_div_of_nonneg_right _ (le_of_lt (by linarith : 0 < 4 * s))
                      apply neg_le_neg
                      nlinarith [sq_nonneg x, sq_nonneg y]
                    have h2 : -(x^2 + y^2) / (4 * s) = -x^2 / (4 * s) + -y^2 / (4 * s) := by ring
                    linarith
                  calc x * y * Real.exp (-(x + y) ^ 2 / (4 * s))
                      ≤ x * y * (Real.exp (-x^2 / (4 * s)) * Real.exp (-y^2 / (4 * s))) := by
                        apply mul_le_mul_of_nonneg_left h_exp_bound
                        apply mul_nonneg (le_of_lt hx) (le_of_lt hy)
                    _ = (x * Real.exp (-x^2 / (4 * s))) * (y * Real.exp (-y^2 / (4 * s))) := by ring
                    _ = (x * Real.exp (-(1/(4*s)) * x^2)) * (y * Real.exp (-(1/(4*s)) * y^2)) := by
                        congr 2 <;> (congr 1; ring)
                    _ = (|x| * Real.exp (-(1/(4*s)) * x^2)) * (y * Real.exp (-(1/(4*s)) * y^2)) :=
                      by
                        rw [abs_of_pos hx]) using 2
          rw [h_fubini]
          -- Now simplify: factor out exp(-u²/(4s)) and compute inner integral
          apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
          intro u hu
          simp only [Set.mem_Ioi] at hu
          -- Goal: ∫_{x₀ ∈ Ioo 0 u} x₀ * (u - x₀) * exp(-u²/(4s)) dx₀ = exp(-u²/(4s)) * (u³/6)
          -- Factor out the exponential (constant w.r.t. x₀)
          have h_factor : ∫ x₀ in Set.Ioo 0 u, x₀ * (u - x₀) * Real.exp (-u^2 / (4 * s)) =
              Real.exp (-u^2 / (4 * s)) * ∫ x₀ in Set.Ioo 0 u, x₀ * (u - x₀) := by
            have h_exp_const : ∀ x₀ : ℝ, x₀ * (u - x₀) * Real.exp (-u^2 / (4 * s)) =
                Real.exp (-u^2 / (4 * s)) * (x₀ * (u - x₀)) := fun x₀ => by ring
            simp_rw [h_exp_const]
            rw [MeasureTheory.integral_const_mul]
          -- The inner integral is ∫_{x₀ ∈ Ioo 0 u} x₀ * (u - x₀) dx₀
          -- Convert to interval integral and use h_poly_int
          have h_inner : ∫ x₀ in Set.Ioo 0 u, x₀ * (u - x₀) = u^3 / 6 := by
            -- ∫ over Ioo 0 u = ∫ over Ioc 0 u = ∫ in 0..u (for continuous functions)
            rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo]
            rw [← intervalIntegral.integral_of_le (le_of_lt hu)]
            exact h_poly_int u hu
          simp only
          rw [h_factor, h_inner]
      _ = (1/6) * ∫ u in Set.Ioi 0, u^3 * Real.exp (-u^2 / (4 * s)) := by
          conv_lhs => arg 2; ext u; rw [show Real.exp (-u^2 / (4 * s)) * (u^3 / 6) =
              (1/6) * (u^3 * Real.exp (-u^2 / (4 * s))) by ring]
          rw [MeasureTheory.integral_const_mul]
      _ = (1/6) * (8 * s^2) := by rw [h_u_int]
  -- Combine the pieces
  calc ∫ x₀ in Set.Ioi 0, ∫ y₀ in Set.Ioi 0,
         x₀ * y₀ * Real.sqrt (π / s) * Real.exp (-(x₀ + y₀)^2 / (4 * s))
      = Real.sqrt (π / s) * ∫ x₀ in Set.Ioi 0, ∫ y₀ in Set.Ioi 0,
          x₀ * y₀ * Real.exp (-(x₀ + y₀)^2 / (4 * s)) := h_pull_const
    _ = Real.sqrt (π / s) * ((1/6) * (8 * s^2)) := by rw [h_double_int]
    _ = Real.sqrt (π / s) * (1/6) * (8 * s^2) := by ring
    _ = (4/3) * Real.sqrt π * s^(3/2 : ℝ) := h_algebra

/-- **Bound version**: The double Gaussian moment integral is bounded by a constant times s^{3/2}.

    This is a weaker form of `heat_kernel_moment_integral` that suffices for
    `F_norm_bound_via_linear_vanishing`.
    The exact value is (4/3)√π · s^{3/2}, so we use 10 · s^{3/2} as a comfortable upper bound.

    **Proof**: Uses `heat_kernel_moment_integral` and the bound (4/3)√π < 10.
-/
lemma heat_kernel_moment_integral_bound (s : ℝ) (hs : 0 < s) :
    ∫ x₀ in Set.Ioi 0, ∫ y₀ in Set.Ioi 0,
      x₀ * y₀ * Real.sqrt (π / s) * Real.exp (-(x₀ + y₀)^2 / (4 * s)) ≤
    10 * s^(3/2 : ℝ) := by
  -- Use the exact equality from heat_kernel_moment_integral
  rw [heat_kernel_moment_integral s hs]
  -- Now show: (4/3) * √π * s^{3/2} ≤ 10 * s^{3/2}
  -- Since (4/3)√π ≈ 2.36 < 10
  have hπ : (4/3 : ℝ) * Real.sqrt π < 10 := by
    have hsqrt : Real.sqrt π < 2 := by
      rw [Real.sqrt_lt' (by norm_num : (0:ℝ) < 2)]
      calc π < 4 := pi_lt_four
         _ = 2^2 := by norm_num
    calc (4/3 : ℝ) * Real.sqrt π < (4/3) * 2 := by nlinarith [Real.sqrt_nonneg π]
      _ = 8/3 := by ring
      _ < 10 := by norm_num
  have hs32 : 0 ≤ s^(3/2 : ℝ) := Real.rpow_nonneg (le_of_lt hs) _
  nlinarith

/-- Helper lemma: t * exp(-b*t²) is integrable on (0, ∞) for b > 0.
    This follows from `integrable_mul_exp_neg_mul_sq` restricted to positive reals.
-/
lemma gaussian_moment_integrableOn_Ioi {b : ℝ} (hb : 0 < b) :
    MeasureTheory.IntegrableOn (fun t => t * Real.exp (-b * t^2)) (Set.Ioi 0) := by
  -- |t| * exp(-b*t²) is integrable on all of ℝ
  have h_int : MeasureTheory.Integrable (fun t => |t| * Real.exp (-b * t^2)) volume := by
    have := integrable_mul_exp_neg_mul_sq hb
    convert this.norm using 1
    ext t; rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  -- Restrict to Ioi 0 and use that t = |t| for t > 0
  rw [MeasureTheory.IntegrableOn]
  apply MeasureTheory.Integrable.mono (h_int.restrict)
  · fun_prop
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [Set.mem_Ioi] at ht
    -- ‖t * exp(-b*t²)‖ = |t * exp(-b*t²)| = t * exp(-b*t²) (since t > 0 and exp > 0)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_of_lt ht) (Real.exp_nonneg _))]
    -- ‖|t| * exp(-b*t²)‖ = |t| * exp(-b*t²) = t * exp(-b*t²) (since t > 0)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_nonneg _))]
    rw [abs_of_pos ht]

/-- Helper lemma: For s > 0 and any t₁ ≥ 0, the function t₂ ↦ t₂ * exp(-(t₁+t₂)²/(4s))
    is integrable on (0, ∞). This is the key integrability fact for heat kernel moment bounds.

    **Proof**: For t₁, t₂ ≥ 0, we have (t₁+t₂)² ≥ t₂², so
    exp(-(t₁+t₂)²/(4s)) ≤ exp(-t₂²/(4s)), and the integrand is dominated by
    t₂ * exp(-t₂²/(4s)) which is integrable by `gaussian_moment_integrableOn_Ioi`.
-/
lemma heat_kernel_inner_integrableOn {s t₁ : ℝ} (hs : 0 < s) (ht₁ : 0 ≤ t₁) :
    MeasureTheory.IntegrableOn
      (fun t₂ => t₂ * Real.exp (-(t₁ + t₂)^2 / (4 * s))) (Set.Ioi 0) := by
  have hb : 0 < 1 / (4 * s) := by positivity
  have h_dom := gaussian_moment_integrableOn_Ioi hb
  rw [MeasureTheory.IntegrableOn] at h_dom ⊢
  -- Rewrite h_dom to match our goal form: t * exp(-(1/(4s))*t²) = t * exp(-t²/(4s))
  have h_dom' : MeasureTheory.Integrable
      (fun t => t * Real.exp (-t^2 / (4 * s))) (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    convert h_dom using 2 with t
    congr 1
    have h4s : 4 * s ≠ 0 := by linarith
    field_simp
  -- The integrand is dominated by t₂ * exp(-t₂²/(4s)) on Ioi 0
  apply MeasureTheory.Integrable.mono h_dom'
  · fun_prop
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t₂ ht₂
    simp only [Set.mem_Ioi] at ht₂
    -- ‖t₂ * exp(-(t₁+t₂)²/(4s))‖ = t₂ * exp(-(t₁+t₂)²/(4s)) (nonneg for t₂ > 0)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_of_lt ht₂) (Real.exp_nonneg _))]
    -- ‖t₂ * exp(-t₂²/(4s))‖ = t₂ * exp(-t₂²/(4s))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_of_lt ht₂) (Real.exp_nonneg _))]
    -- Need: t₂ * exp(-(t₁+t₂)²/(4s)) ≤ t₂ * exp(-t₂²/(4s))
    apply mul_le_mul_of_nonneg_left _ (le_of_lt ht₂)
    apply Real.exp_le_exp.mpr
    -- Need: -(t₁+t₂)²/(4s) ≤ -t₂²/(4s), i.e., (t₁+t₂)² ≥ t₂²
    apply div_le_div_of_nonneg_right _ (by linarith : 0 ≤ 4 * s)
    apply neg_le_neg
    nlinarith [sq_nonneg t₁]

/-- The heat kernel moment integrand is integrable on the product quadrant (0,∞)².
    This is the key integrability result extracted from heat_kernel_moment_integral.
-/
lemma heat_kernel_moment_integrableOn_quadrant (s : ℝ) (hs : 0 < s) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ × ℝ => z.1 * z.2 * Real.sqrt (π/s) * Real.exp (-(z.1 + z.2)^2 / (4 * s)))
      (Set.Ioi 0 ×ˢ Set.Ioi 0) (volume.prod volume) := by
  rw [MeasureTheory.IntegrableOn]
  have hb : 0 < 1 / (4 * s) := by positivity
  have h_int_factor : MeasureTheory.Integrable
      (fun x => |x| * Real.exp (-(1/(4*s)) * x^2)) volume := by
    have := integrable_mul_exp_neg_mul_sq hb
    convert this.norm using 1
    ext x; rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have h_prod := MeasureTheory.Integrable.mul_prod h_int_factor h_int_factor
  have h_prod_restr : MeasureTheory.Integrable
      (fun z : ℝ × ℝ => |z.1| * Real.exp (-(1/(4*s)) * z.1^2) *
                        (|z.2| * Real.exp (-(1/(4*s)) * z.2^2)))
      (volume.restrict (Set.Ioi 0 ×ˢ Set.Ioi 0)) := by
    rw [MeasureTheory.Measure.volume_eq_prod]
    exact h_prod.restrict (s := Set.Ioi 0 ×ˢ Set.Ioi 0)
  -- Dominate by √(π/s) * h_prod_restr
  apply MeasureTheory.Integrable.mono (h_prod_restr.const_mul (Real.sqrt (π/s)))
  · fun_prop
  · filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)]
      with ⟨x, y⟩ hxy
    simp only [Set.mem_prod, Set.mem_Ioi] at hxy
    obtain ⟨hx, hy⟩ := hxy
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have h_lhs_nonneg : 0 ≤ x * y * Real.sqrt (π / s) * Real.exp (-(x + y) ^ 2 / (4 * s)) := by
      positivity
    rw [abs_of_nonneg h_lhs_nonneg]
    have h_rhs_inner_nonneg : 0 ≤ |x| * Real.exp (-(1/(4*s)) * x^2) *
        (|y| * Real.exp (-(1/(4*s)) * y^2)) := by positivity
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg h_rhs_inner_nonneg]
    rw [abs_of_nonneg (le_of_lt hx), abs_of_nonneg (le_of_lt hy)]
    have h_sqrt_nonneg : 0 ≤ Real.sqrt (π / s) := Real.sqrt_nonneg _
    rw [show x * y * Real.sqrt (π / s) * Real.exp (-(x + y) ^ 2 / (4 * s)) =
        Real.sqrt (π / s) * (x * y * Real.exp (-(x + y) ^ 2 / (4 * s))) by ring]
    apply mul_le_mul_of_nonneg_left _ h_sqrt_nonneg
    have hsum : (x + y)^2 ≥ x^2 + y^2 := by nlinarith [sq_nonneg x, sq_nonneg y, mul_pos hx hy]
    have hexp : Real.exp (-(x+y)^2/(4*s)) ≤ Real.exp (-(x^2 + y^2)/(4*s)) := by
      apply Real.exp_le_exp_of_le
      apply div_le_div_of_nonneg_right _ (le_of_lt (by linarith : 0 < 4*s))
      linarith [hsum]
    have hexp_factor : Real.exp (-(x^2 + y^2)/(4*s)) =
        Real.exp (-(1/(4*s)) * x^2) * Real.exp (-(1/(4*s)) * y^2) := by
      rw [← Real.exp_add]; congr 1; field_simp; ring
    calc x * y * Real.exp (-(x + y)^2 / (4 * s))
        ≤ x * y * Real.exp (-(x^2 + y^2)/(4*s)) := by
          nlinarith [Real.exp_nonneg (-(x^2 + y^2)/(4*s))]
      _ = x * y * (Real.exp (-(1/(4*s)) * x^2) * Real.exp (-(1/(4*s)) * y^2)) := by rw [hexp_factor]
      _ = x * Real.exp (-(1/(4*s)) * x^2) * (y * Real.exp (-(1/(4*s)) * y^2)) := by ring

/-! ### Heat Kernel Moment - Extended by Zero

The key technique for proving integrability of parametric set integrals is to extend
the integrand to be zero outside the region of interest, then use global Fubini theorems.
-/

/-- Heat kernel moment integrand extended by zero outside (0,∞)².
    F(t₁, t₂) = t₁ · t₂ · √(π/s) · exp(-(t₁+t₂)²/(4s)) for t₁, t₂ > 0, else 0.
-/
def heatKernelMomentExt (s : ℝ) : ℝ × ℝ → ℝ := fun p =>
  if p.1 > 0 ∧ p.2 > 0 then
    p.1 * p.2 * Real.sqrt (π / s) * Real.exp (-(p.1 + p.2)^2 / (4 * s))
  else 0

/-- The extended heat kernel moment function is integrable on ℝ².

    **Proof**: The function is nonnegative and has finite integral
    (equal to (π/2)·s^{3/2} by heat_kernel_moment_integral), hence integrable.

    Mathematical justification: For nonnegative measurable f, ∫ f < ∞ implies Integrable f
    (Tonelli's theorem). Here f = heatKernelMomentExt and ∫ f = (π/2)·s^{3/2}.

    **Reference**: Rudin "Real and Complex Analysis" Ch.8 (Tonelli).
-/
lemma heatKernelMomentExt_integrable (s : ℝ) (hs : 0 < s) :
    MeasureTheory.Integrable (heatKernelMomentExt s) (volume.prod volume) := by
  -- heatKernelMomentExt is the indicator of the heat kernel moment on (0,∞)²
  have h_eq : heatKernelMomentExt s = (Set.Ioi 0 ×ˢ Set.Ioi 0).indicator
      (fun z : ℝ × ℝ => z.1 * z.2 * Real.sqrt (π/s) * Real.exp (-(z.1 + z.2)^2 / (4 * s))) := by
    ext ⟨t₁, t₂⟩
    unfold heatKernelMomentExt
    by_cases h : t₁ > 0 ∧ t₂ > 0
    · simp only [h, Set.indicator_apply, Set.mem_prod, Set.mem_Ioi]
    · simp only [h, ↓reduceIte, Set.indicator_apply, Set.mem_prod, Set.mem_Ioi]
  rw [h_eq]
  apply MeasureTheory.IntegrableOn.integrable_indicator _
      (measurableSet_Ioi.prod measurableSet_Ioi)
  exact heat_kernel_moment_integrableOn_quadrant s hs

/-- Parametric integral of extended heat kernel moment is integrable on ℝ.

    This follows from Fubini's theorem: if f is integrable on the product,
    then t₁ ↦ ∫ t₂, f(t₁, t₂) is integrable.
-/
lemma heatKernelMomentExt_parametric_integrable (s : ℝ) (hs : 0 < s) :
    MeasureTheory.Integrable (fun t₁ => ∫ t₂, heatKernelMomentExt s (t₁, t₂)) volume :=
  (heatKernelMomentExt_integrable s hs).integral_prod_left

/-- The parametric integral of the extended function gives a set integral for t₁ > 0. -/
lemma heatKernelMomentExt_parametric_eq_setIntegral (s : ℝ) (t₁ : ℝ) (ht₁ : 0 < t₁) :
    ∫ t₂, heatKernelMomentExt s (t₁, t₂) =
    ∫ t₂ in Set.Ioi 0, t₁ * t₂ * Real.sqrt (π / s) * Real.exp (-(t₁ + t₂)^2 / (4 * s)) := by
  have h_eq : ∀ t₂, heatKernelMomentExt s (t₁, t₂) =
      (Set.Ioi 0).indicator (fun t₂ => t₁ * t₂ * Real.sqrt (π / s) *
        Real.exp (-(t₁ + t₂)^2 / (4 * s))) t₂ := by
    intro t₂
    unfold heatKernelMomentExt
    by_cases ht₂ : t₂ > 0
    · simp only [ht₁, ht₂, and_self, ↓reduceIte, Set.indicator_apply, Set.mem_Ioi]
    · push Not at ht₂
      simp only [not_lt.mpr ht₂, and_false, ↓reduceIte, Set.indicator_apply, Set.mem_Ioi]
  simp_rw [h_eq]
  rw [MeasureTheory.integral_indicator measurableSet_Ioi]

/-- **Key lemma**: The parametric set integral of heat kernel moments is integrable on (0,∞).

    For any constant c ≥ 0, the function t₁ ↦ ∫_{t₂ > 0} c·t₁·t₂·K(t₁,t₂) dt₂
    is integrable on (0,∞).

    **Proof sketch**:
    1. heatKernelMomentExt is integrable on ℝ² (sorry - uses Tonelli + finite integral)
    2. By Fubini, t₁ ↦ ∫ t₂, heatKernelMomentExt(t₁,t₂) is integrable on ℝ
    3. The set integral on (0,∞) equals the full integral (zero outside)
    4. Multiply by constant c preserves integrability
-/
lemma heatKernelMoment_setIntegral_integrableOn (s : ℝ) (hs : 0 < s) (c : ℝ) :
    MeasureTheory.IntegrableOn
      (fun t₁ => ∫ t₂ in Set.Ioi 0,
        c * t₁ * t₂ * Real.sqrt (π / s) * Real.exp (-(t₁ + t₂)^2 / (4 * s)))
      (Set.Ioi 0) := by
  -- Rewrite the integrand in terms of heatKernelMomentExt
  have h_eq : ∀ t₁ ∈ Set.Ioi (0:ℝ),
      (∫ t₂ in Set.Ioi 0, c * t₁ * t₂ * Real.sqrt (π / s) * Real.exp (-(t₁ + t₂)^2 / (4 * s))) =
      c * (∫ t₂, heatKernelMomentExt s (t₁, t₂)) := by
    intro t₁ ht₁
    rw [heatKernelMomentExt_parametric_eq_setIntegral s t₁ ht₁]
    -- Factor out c
    rw [← MeasureTheory.integral_const_mul]
    congr 1; ext t₂; ring
  -- The parametric integral of heatKernelMomentExt is integrable
  have h_param := heatKernelMomentExt_parametric_integrable s hs
  -- Restrict to Ioi 0 and scale by c
  have h_intOn : MeasureTheory.IntegrableOn
      (fun t₁ => ∫ t₂, heatKernelMomentExt s (t₁, t₂)) (Set.Ioi 0) :=
    h_param.integrableOn
  have h_scaled : MeasureTheory.IntegrableOn
      (fun t₁ => c * (∫ t₂, heatKernelMomentExt s (t₁, t₂))) (Set.Ioi 0) :=
    h_intOn.const_mul c
  -- The goal function equals the scaled function on Ioi 0
  apply h_scaled.congr
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t₁ ht₁
  exact (h_eq t₁ ht₁).symm

private lemma heat_kernel_spatial_integral_bound (s : ℝ) (hs : 0 < s)
    (C_sp : ℝ) (hC_sp_pos : 0 < C_sp) (G : ℝ → ℝ)
    (hG_zero : ∀ t ≤ 0, G t = 0)
    (hG_nonneg : ∀ t, 0 ≤ G t)
    (hG_meas : Measurable G)
    (h_spatial : ∀ t, 0 < t → G t ≤ C_sp * t) :
    ∫ t₁ : ℝ, ∫ t₂ : ℝ,
      Real.sqrt (π / s) * Real.exp (-(t₁ + t₂)^2 / (4 * s)) * G t₁ * G t₂
        ≤ C_sp^2 * (10 * s^(3/2 : ℝ)) := by
  let K := fun t₁ t₂ => Real.sqrt (π / s) * Real.exp (-(t₁ + t₂)^2 / (4 * s))
  have hK_nonneg : ∀ t₁ t₂, 0 ≤ K t₁ t₂ := fun _ _ =>
    mul_nonneg (Real.sqrt_nonneg _) (Real.exp_nonneg _)
  have hK_meas : Measurable (Function.uncurry K) := by
    simp only [K]
    fun_prop
  have h_supp_inner : ∀ t₁ : ℝ, ∫ t₂ : ℝ, K t₁ t₂ * G t₁ * G t₂ =
      ∫ t₂ in Set.Ioi 0, K t₁ t₂ * G t₁ * G t₂ := by
    intro t₁
    symm
    apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t₂ ht₂
    simp only [Set.mem_Ioi, not_lt] at ht₂
    simp only [hG_zero t₂ ht₂, mul_zero]
  have h_supp_outer : ∫ t₁ : ℝ, ∫ t₂ in Set.Ioi 0, K t₁ t₂ * G t₁ * G t₂ =
      ∫ t₁ in Set.Ioi 0, ∫ t₂ in Set.Ioi 0, K t₁ t₂ * G t₁ * G t₂ := by
    symm
    apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t₁ ht₁
    simp only [Set.mem_Ioi, not_lt] at ht₁
    simp only [hG_zero t₁ ht₁, mul_zero, zero_mul, MeasureTheory.integral_zero]
  have h_bound : ∀ t₁ ∈ Set.Ioi (0:ℝ), ∀ t₂ ∈ Set.Ioi (0:ℝ),
      K t₁ t₂ * G t₁ * G t₂ ≤ K t₁ t₂ * (C_sp * t₁) * (C_sp * t₂) := by
    intro t₁ ht₁ t₂ ht₂
    simp only [Set.mem_Ioi] at ht₁ ht₂
    apply mul_le_mul
    · apply mul_le_mul (le_refl _) (h_spatial t₁ ht₁) (hG_nonneg t₁) (hK_nonneg t₁ t₂)
    · exact h_spatial t₂ ht₂
    · exact hG_nonneg t₂
    · apply mul_nonneg (hK_nonneg t₁ t₂); exact mul_nonneg hC_sp_pos.le (le_of_lt ht₁)
  have h_mono_inner : ∀ t₁ ∈ Set.Ioi (0:ℝ),
      ∫ t₂ in Set.Ioi 0, K t₁ t₂ * G t₁ * G t₂ ≤
      ∫ t₂ in Set.Ioi 0, K t₁ t₂ * (C_sp * t₁) * (C_sp * t₂) := by
    intro t₁ ht₁
    simp only [Set.mem_Ioi] at ht₁
    apply MeasureTheory.setIntegral_mono_on
    · have h_inner := heat_kernel_inner_integrableOn hs (le_of_lt ht₁)
      rw [MeasureTheory.IntegrableOn]
      have h_dom : MeasureTheory.Integrable
          (fun t₂ => K t₁ t₂ * (C_sp * t₁) * (C_sp * t₂)) (volume.restrict (Set.Ioi 0)) := by
        have h1 : (fun t₂ => K t₁ t₂ * (C_sp * t₁) * (C_sp * t₂)) =
            (fun t₂ => C_sp^2 * t₁ * Real.sqrt (π / s) *
              (t₂ * Real.exp (-(t₁ + t₂)^2 / (4 * s)))) := by
          ext t₂; simp only [K]; ring
        rw [h1]
        exact h_inner.const_mul (C_sp^2 * t₁ * Real.sqrt (π / s))
      apply MeasureTheory.Integrable.mono h_dom
      · have hKt₁ : Measurable (fun t₂ => K t₁ t₂) := Measurable.of_uncurry_left hK_meas
        fun_prop (disch := assumption)
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t₂ ht₂
        simp only [Set.mem_Ioi] at ht₂
        rw [Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (mul_nonneg (hK_nonneg t₁ t₂) (hG_nonneg t₁))
            (hG_nonneg t₂))]
        rw [Real.norm_eq_abs]
        rw [abs_of_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
          (Real.exp_nonneg _))
          (mul_nonneg hC_sp_pos.le (le_of_lt ht₁))) (mul_nonneg hC_sp_pos.le (le_of_lt ht₂)))]
        exact h_bound t₁ (Set.mem_Ioi.mpr ht₁) t₂ (Set.mem_Ioi.mpr ht₂)
    · have h_inner := heat_kernel_inner_integrableOn hs (le_of_lt ht₁)
      rw [MeasureTheory.IntegrableOn]
      apply MeasureTheory.Integrable.mono (h_inner.const_mul (C_sp^2 * t₁ * Real.sqrt (π / s)))
      · have hKt₁ : Measurable (fun t₂ => K t₁ t₂) := Measurable.of_uncurry_left hK_meas
        fun_prop (disch := assumption)
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t₂ ht₂
        simp only [Set.mem_Ioi] at ht₂
        simp only [K]
        rw [Real.norm_eq_abs]
        rw [abs_of_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
          (Real.exp_nonneg _))
          (mul_nonneg hC_sp_pos.le (le_of_lt ht₁))) (mul_nonneg hC_sp_pos.le (le_of_lt ht₂)))]
        rw [Real.norm_eq_abs]
        have hconst_nonneg : 0 ≤ C_sp^2 * t₁ * Real.sqrt (π / s) :=
          mul_nonneg (mul_nonneg (sq_nonneg _) (le_of_lt ht₁)) (Real.sqrt_nonneg _)
        rw [abs_of_nonneg (mul_nonneg hconst_nonneg (mul_nonneg (le_of_lt ht₂)
          (Real.exp_nonneg _)))]
        have h_eq : Real.sqrt (π / s) * Real.exp (-(t₁ + t₂)^2 / (4 * s)) * (C_sp * t₁) *
          (C_sp * t₂)
            = C_sp^2 * t₁ * Real.sqrt (π / s) * (t₂ * Real.exp (-(t₁ + t₂)^2 / (4 * s))) :=
              by ring
        exact le_of_eq h_eq
    · exact measurableSet_Ioi
    · intro t₂ ht₂; exact h_bound t₁ ht₁ t₂ ht₂
  have h_mono_outer :
      ∫ t₁ in Set.Ioi 0, ∫ t₂ in Set.Ioi 0, K t₁ t₂ * G t₁ * G t₂ ≤
      ∫ t₁ in Set.Ioi 0, ∫ t₂ in Set.Ioi 0, K t₁ t₂ * (C_sp * t₁) * (C_sp * t₂) := by
    apply MeasureTheory.setIntegral_mono_on
    · have h_g_integrableOn : MeasureTheory.IntegrableOn
          (fun t₁ => ∫ t₂ in Set.Ioi 0, K t₁ t₂ * (C_sp * t₁) * (C_sp * t₂)) (Set.Ioi 0) := by
        have h_eq : ∀ t₁ t₂ : ℝ, K t₁ t₂ * (C_sp * t₁) * (C_sp * t₂) =
            C_sp^2 * t₁ * t₂ * Real.sqrt (π / s) * Real.exp (-(t₁ + t₂)^2 / (4 * s)) := by
          intro t₁ t₂; simp only [K]; ring
        simp_rw [h_eq]
        exact heatKernelMoment_setIntegral_integrableOn s hs (C_sp^2)
      rw [MeasureTheory.IntegrableOn] at h_g_integrableOn ⊢
      apply MeasureTheory.Integrable.mono h_g_integrableOn
      · have h_joint_meas : Measurable (fun p : ℝ × ℝ => K p.1 p.2 * G p.1 * G p.2) := by
          have hKp : Measurable (fun p : ℝ × ℝ => K p.1 p.2) := hK_meas
          fun_prop (disch := assumption)
        exact (h_joint_meas.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t₁ ht₁
        simp only [Set.mem_Ioi] at ht₁
        rw [Real.norm_eq_abs, abs_of_nonneg, Real.norm_eq_abs, abs_of_nonneg]
        · exact h_mono_inner t₁ (Set.mem_Ioi.mpr ht₁)
        · apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
          intro t₂ ht₂; simp only [Set.mem_Ioi] at ht₂
          apply mul_nonneg
          · apply mul_nonneg (hK_nonneg t₁ t₂)
            exact mul_nonneg hC_sp_pos.le (le_of_lt ht₁)
          · exact mul_nonneg hC_sp_pos.le (le_of_lt ht₂)
        · apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
          intro t₂ ht₂
          apply mul_nonneg
          · exact mul_nonneg (hK_nonneg t₁ t₂) (hG_nonneg t₁)
          · exact hG_nonneg t₂
    · have h_eq : ∀ t₁ t₂ : ℝ, K t₁ t₂ * (C_sp * t₁) * (C_sp * t₂) =
          C_sp^2 * t₁ * t₂ * Real.sqrt (π / s) * Real.exp (-(t₁ + t₂)^2 / (4 * s)) := by
        intro t₁ t₂; simp only [K]; ring
      simp_rw [h_eq]
      exact heatKernelMoment_setIntegral_integrableOn s hs (C_sp^2)
    · exact measurableSet_Ioi
    · intro t₁ ht₁; exact h_mono_inner t₁ ht₁
  have h_final :
      ∫ t₁ in Set.Ioi 0, ∫ t₂ in Set.Ioi 0, K t₁ t₂ * (C_sp * t₁) * (C_sp * t₂) =
      C_sp^2 * ∫ t₁ in Set.Ioi 0, ∫ t₂ in Set.Ioi 0,
        t₁ * t₂ * Real.sqrt (π / s) * Real.exp (-(t₁ + t₂)^2 / (4 * s)) := by
    have h_eq : ∀ t₁ t₂ : ℝ, K t₁ t₂ * (C_sp * t₁) * (C_sp * t₂) =
        C_sp^2 * (t₁ * t₂ * Real.sqrt (π / s) * Real.exp (-(t₁ + t₂)^2 / (4 * s))) := by
      intro t₁ t₂; simp only [K]; ring
    have h_lhs : ∫ t₁ in Set.Ioi 0, ∫ t₂ in Set.Ioi 0, K t₁ t₂ * (C_sp * t₁) * (C_sp * t₂) =
        ∫ t₁ in Set.Ioi 0, ∫ t₂ in Set.Ioi 0,
          C_sp^2 * (t₁ * t₂ * Real.sqrt (π / s) * Real.exp (-(t₁ + t₂)^2 / (4 * s))) := by
      congr 1; ext t₁; congr 1; ext t₂; exact h_eq t₁ t₂
    rw [h_lhs]
    simp_rw [MeasureTheory.integral_const_mul]
  calc ∫ t₁ : ℝ, ∫ t₂ : ℝ, K t₁ t₂ * G t₁ * G t₂
      = ∫ t₁ in Set.Ioi 0, ∫ t₂ in Set.Ioi 0, K t₁ t₂ * G t₁ * G t₂ := by
        simp_rw [h_supp_inner, h_supp_outer]
    _ ≤ ∫ t₁ in Set.Ioi 0, ∫ t₂ in Set.Ioi 0, K t₁ t₂ * (C_sp * t₁) * (C_sp * t₂) :=
        h_mono_outer
    _ = C_sp^2 * ∫ t₁ in Set.Ioi 0, ∫ t₂ in Set.Ioi 0,
          t₁ * t₂ * Real.sqrt (π / s) * Real.exp (-(t₁ + t₂)^2 / (4 * s)) :=
        h_final
    _ ≤ C_sp^2 * (10 * s^(3/2 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left (heat_kernel_moment_integral_bound s hs)
        positivity

/-- Fubini factorization for Schwartz functions with linear vanishing.

    For Schwartz f : SpaceTime → ℂ vanishing at t ≤ 0, the double integral with
    heat kernel factor is bounded by K · s^{3/2} for some constant K > 0.

    **Proof strategy** (Tonelli factorization):
    1. Use `spatialNormIntegral_linear_bound`: G(t) := ∫_{ℝ³} ‖f(t,x)‖ dx ≤ C_sp · t
    2. Factor via Tonelli: ∫∫_{SpaceTime²} = ∫_{time²} G(t₁)·G(t₂) · √(π/s)·exp(...)
    3. Bound: ≤ C_sp² · ∫_{time²} t₁·t₂ · √(π/s)·exp(-(t₁+t₂)²/(4s))
    4. Apply `heat_kernel_moment_integral_bound`: ≤ C_sp² · 10 · s^{3/2}

    **Reference**: Rudin "Real and Complex Analysis" Ch.8 (Fubini);
                  Standard heat kernel estimates.
-/
lemma spacetime_fubini_linear_vanishing_bound (f : TestFunctionℂ)
    (hf_supp : ∀ x : SpaceTime, x 0 ≤ 0 → f x = 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ (s : ℝ) (_hs : 0 < s),
      ∫ x : SpaceTime, ∫ y : SpaceTime, ‖f x‖ * ‖f y‖ * Real.sqrt (π / s) *
        Real.exp (-(x 0 + y 0)^2 / (4 * s)) ≤ K * s^(3/2 : ℝ) := by
  -- Step 1: Get the spatial integral linear bound (independent of s)
  obtain ⟨C_sp, hC_sp_pos, h_spatial⟩ := spatialNormIntegral_linear_bound f hf_supp
  use C_sp^2 * 10
  constructor
  · positivity
  -- Step 2: For any s > 0, prove the bound
  intro s hs
  -- We have the spatial integral bound: G(t) := ∫_{ℝ³} ‖f(t,x_sp)‖ dx_sp ≤ C_sp · t for t > 0
  -- (from h_spatial : spatialNormIntegral_linear_bound f hf_supp)
  -- The integrand is non-negative
  have h_nn : ∀ x y : SpaceTime,
      0 ≤ ‖f x‖ * ‖f y‖ * Real.sqrt (π / s) * Real.exp (-(x 0 + y 0)^2 / (4 * s)) := by
    intro x y
    apply mul_nonneg
    · apply mul_nonneg
      · exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
      · exact Real.sqrt_nonneg _
    · exact Real.exp_nonneg _
  -- Tonelli factorization: ∫∫_{SpaceTime²} = ∫_{time²} G(t₁)·G(t₂)·√(π/s)·exp(-(t₁+t₂)²/(4s))
  -- where G(t) := ∫_{ℝ³} ‖f(t,·)‖, then bound G(t) ≤ C_sp·t (h_spatial, G=0 for t≤0) and apply
  -- heat_kernel_moment_integral_bound to get ≤ C_sp²·10·s^{3/2}.
  let G := spatialNormIntegral f
  -- G(t) = 0 for t ≤ 0 (by support condition)
  have hG_zero : ∀ t ≤ 0, G t = 0 := fun t ht => spatialNormIntegral_zero_of_neg f hf_supp t ht
  -- G is nonnegative
  have hG_nonneg : ∀ t, 0 ≤ G t := fun t => spatialNormIntegral_nonneg f t
  -- G is measurable (via strongly measurable)
  -- Uses: f is Schwartz (continuous), so (t, x_sp) ↦ ‖f(spacetimeOfTimeSpace t x_sp)‖ is continuous
  -- Then t ↦ ∫ x_sp, ‖f(...)‖ is strongly measurable by integral_prod_right
  have hG_meas : Measurable G := by
    -- G t = ∫ x_sp, ‖f (spacetimeOfTimeSpace t x_sp)‖
    -- First prove spacetimeOfTimeSpace is continuous as a function of (t, x_sp)
    have h_sts_cont : Continuous (Function.uncurry spacetimeOfTimeSpace) := by
      -- spacetimeOfTimeSpace t x = EuclideanSpace.equiv ... |>.symm (Fin.cons t (fun i => x i))
      -- This is a composition of continuous functions
      unfold spacetimeOfTimeSpace Function.uncurry
      apply (EuclideanSpace.equiv (Fin 4) ℝ).symm.continuous.comp
      -- Need: Continuous (fun p : ℝ × SpatialCoords3 => Fin.cons p.1 (fun i => p.2 i))
      apply continuous_pi
      intro j
      cases j using Fin.cases with
      | zero =>
        simpa only [Fin.cons_zero] using continuous_fst
      | succ j =>
        simp only [Fin.cons_succ]
        exact (PiLp.continuous_apply 2 _ j).comp continuous_snd
    -- The joint function (t, x_sp) ↦ ‖f(spacetimeOfTimeSpace t x_sp)‖ is continuous
    have h_joint_cont : Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin 3) =>
        ‖f (spacetimeOfTimeSpace p.1 p.2)‖) := by
      apply Continuous.norm
      exact (SchwartzMap.continuous f).comp h_sts_cont
    -- Continuous implies strongly measurable
    have h_joint_sm : MeasureTheory.StronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin 3) =>
        ‖f (spacetimeOfTimeSpace p.1 p.2)‖) := h_joint_cont.stronglyMeasurable
    -- Use StronglyMeasurable.integral_prod_right
    have h_sm : MeasureTheory.StronglyMeasurable (fun t => ∫ x_sp,
      ‖f (spacetimeOfTimeSpace t x_sp)‖) :=
      MeasureTheory.StronglyMeasurable.integral_prod_right h_joint_sm
    exact h_sm.measurable
  -- The heat kernel factor
  let K := fun t₁ t₂ => Real.sqrt (π / s) * Real.exp (-(t₁ + t₂)^2 / (4 * s))
  have hK_nonneg : ∀ t₁ t₂, 0 ≤ K t₁ t₂ := fun _ _ =>
    mul_nonneg (Real.sqrt_nonneg _) (Real.exp_nonneg _)
  -- Step 2: The integrand factors as G(t₁) * G(t₂) * K(t₁, t₂) after Tonelli
  -- This is the key Tonelli step: decompose SpaceTime × SpaceTime ≃ (ℝ × ℝ) × (ℝ³ × ℝ³)
  -- and factor the spatial integrals.
  --
  -- ∫∫_{SpaceTime²} ‖f x‖·‖f y‖·K(x₀,y₀) dx dy
  -- = ∫∫_{ℝ²} K(t₁,t₂) · [∫_{ℝ³} ‖f(t₁,·)‖] · [∫_{ℝ³} ‖f(t₂,·)‖] dt₁ dt₂  [Tonelli]
  -- = ∫∫_{ℝ²} K(t₁,t₂) · G(t₁) · G(t₂) dt₁ dt₂
  -- Step 3: Bound using G(t) ≤ C_sp * t for t > 0
  -- Since G(t) = 0 for t ≤ 0, the integral restricts to (0,∞)²
  -- On (0,∞)², G(t₁) * G(t₂) ≤ C_sp² * t₁ * t₂
  -- Step 4: Apply heat_kernel_moment_integral_bound
  -- ∫∫_{(0,∞)²} t₁ * t₂ * K(t₁,t₂) dt₁ dt₂ ≤ 10 * s^{3/2}
  -- The kernel K is measurable
  have hK_meas : Measurable (Function.uncurry K) := by
    simp only [K]
    fun_prop
  -- Apply Tonelli factorization theorem (schwartz_tonelli_spacetime)
  -- This gives: ∫∫_{SpaceTime²} ‖f x‖ · ‖f y‖ · K(x₀,y₀) = ∫∫_{ℝ²} K(t₁,t₂) · G(t₁) · G(t₂) dt
  have hK_bdd : ∃ C : ℝ, ∀ t₁ t₂, K t₁ t₂ ≤ C := by
    use Real.sqrt (π / s)
    intro t₁ t₂
    calc K t₁ t₂ = Real.sqrt (π / s) * Real.exp (-(t₁ + t₂)^2 / (4 * s)) := rfl
      _ ≤ Real.sqrt (π / s) * 1 := by
          apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
          rw [Real.exp_le_one_iff]
          apply div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _))
          linarith
      _ = Real.sqrt (π / s) := mul_one _
  have h_tonelli := schwartz_tonelli_spacetime f f K hK_nonneg hK_meas hK_bdd
  -- G from h_tonelli matches spatialNormIntegral via the linking lemma
  have hG_eq : (fun t => ∫ v : SpatialCoords, ‖f (spacetimeDecomp.symm (t, v))‖) = G := by
    ext t
    simp only [G, spatialNormIntegral]
    apply integral_congr_ae
    filter_upwards with v
    rw [spacetimeDecomp_symm_eq_spacetimeOfTimeSpace]
  -- The integrand matches K(x 0, y 0)
  have h_integrand : ∀ x y : SpaceTime,
      ‖f x‖ * ‖f y‖ * Real.sqrt (π / s) * Real.exp (-(x 0 + y 0)^2 / (4 * s)) =
      ‖f x‖ * ‖f y‖ * K (x 0) (y 0) := fun x y => by ring
  -- Define the bounded version: H(t) = C_sp * max(t, 0)
  -- G(t) ≤ H(t) for all t: when t > 0 by h_spatial, when t ≤ 0 because G = 0
  have hG_bound : ∀ t, G t ≤ C_sp * max t 0 := by
    intro t
    by_cases ht : 0 < t
    · have h1 : G t ≤ C_sp * t := h_spatial t ht
      simpa only [max_eq_left (le_of_lt ht)] using h1
    · push Not at ht
      have h1 : G t = 0 := hG_zero t ht
      simp only [h1, max_eq_right ht, mul_zero, le_refl]
  -- Bound: K * G(t₁) * G(t₂) ≤ K * C_sp² * max(t₁,0) * max(t₂,0)
  have h_pointwise_bound : ∀ t₁ t₂,
      K t₁ t₂ * G t₁ * G t₂ ≤ K t₁ t₂ * (C_sp * max t₁ 0) * (C_sp * max t₂ 0) := by
    intro t₁ t₂
    apply mul_le_mul
    · apply mul_le_mul (le_refl _) (hG_bound t₁) (hG_nonneg t₁) (hK_nonneg t₁ t₂)
    · exact hG_bound t₂
    · exact hG_nonneg t₂
    · apply mul_nonneg (hK_nonneg t₁ t₂)
      exact mul_nonneg hC_sp_pos.le (le_max_right t₁ 0)
  -- The main bound using direct calculation on (0,∞)²
  -- Key idea: G(t) = 0 for t ≤ 0, so the ℝ² integral equals the (0,∞)² integral
  -- On (0,∞)², we can use h_spatial: G(t) ≤ C_sp * t
  calc ∫ x : SpaceTime, ∫ y : SpaceTime,
          ‖f x‖ * ‖f y‖ * Real.sqrt (π / s) * Real.exp (-(x 0 + y 0)^2 / (4 * s))
      = ∫ x : SpaceTime, ∫ y : SpaceTime, ‖f x‖ * ‖f y‖ * K (x 0) (y 0) := by
        congr 1; ext x; congr 1; ext y; exact h_integrand x y
    _ = ∫ t₁ : ℝ, ∫ t₂ : ℝ, K t₁ t₂ * G t₁ * G t₂ := by
        have h := h_tonelli
        dsimp only at h
        -- h : LHS = ∫ t₁ t₂, (K t₁ t₂ * ∫ v, ...) * ∫ v, ...
        -- goal: LHS = ∫ t₁ t₂, K t₁ t₂ * G t₁ * G t₂
        exact h.trans (by
          congr 1; ext t₁; congr 1; ext t₂
          congr 1
          · congr 1
            exact congr_fun hG_eq t₁
          · exact congr_fun hG_eq t₂)
    _ ≤ C_sp^2 * (10 * s^(3/2 : ℝ)) := by
        simpa [K] using heat_kernel_spatial_integral_bound s hs C_sp hC_sp_pos G
          hG_zero hG_nonneg hG_meas h_spatial
    _ = C_sp^2 * 10 * s^(3/2 : ℝ) := by ring

/-- **Schwartz norm–Gaussian product measurability.**

    For Schwartz f : SpaceTime → ℂ, constants c₁, c₂ ∈ ℝ, s > 0, and fixed x : SpaceTime,
    the function a ↦ ‖f x‖ * ‖f a‖ * c₁ * exp(-(x₀ + a₀)²/(4s)) * c₂ is AEStronglyMeasurable.

    **Mathematical content:**
    This is standard: norms of Schwartz functions are continuous (hence measurable),
    Gaussian functions are continuous, and products/scalar multiples of measurable
    functions are measurable.

    **Reference**: Rudin "Real and Complex Analysis" Ch.1 (measurable functions);
                  Folland "Real Analysis" Ch.2.
-/
lemma schwartz_heat_product_aestronglymeasurable (f : TestFunctionℂ)
    (x : SpaceTime) (c₁ c₂ : ℝ) (s : ℝ) (_hs : 0 < s) :
    AEStronglyMeasurable (fun a : SpaceTime =>
      ‖f x‖ * ‖f a‖ * c₁ * Real.exp (-(x 0 + a 0)^2 / (4 * s)) * c₂) volume := by
  have h0 : Continuous (fun a : SpaceTime => a 0) := by
    simpa using (PiLp.continuous_apply 2 (fun _ : Fin STDimension => ℝ) (0 : Fin STDimension))
  have hf : Continuous f := f.continuous
  fun_prop (disch := assumption)

/-- **Iterated integral integrability for Schwartz-bounded functions.**

    For Schwartz f : SpaceTime → ℂ and bounded factors (√(π/s), exp(-sω²)),
    the function x ↦ ∫_y ‖f x‖ · ‖f y‖ · √(π/s) · exp(-(x₀+y₀)²/(4s)) · exp(-sω²) is integrable.

    **Mathematical content:**
    By Fubini/Tonelli, if ∫∫ |F(x,y)| < ∞, then ∫_y |F(x,y)| is integrable in x.
    Here F(x,y) = ‖f x‖ · ‖f y‖ · (bounded factors), and the double integral is finite
    by spacetime_fubini_linear_vanishing_bound (using linear vanishing) or by
    direct Schwartz decay estimates.

    **Reference**: Rudin "Real and Complex Analysis" Ch.8 (Fubini);
                  Folland "Real Analysis" Ch.2 (Tonelli).
-/
lemma schwartz_iterated_integral_integrable (f : TestFunctionℂ)
    (hf_int_norm : Integrable (fun x => ‖f x‖) volume)
    (c₁ c₂ : ℝ) (s : ℝ) (hs : 0 < s) :
    Integrable (fun x : SpaceTime => ∫ y : SpaceTime,
      ‖f x‖ * ‖f y‖ * c₁ * Real.exp (-(x 0 + y 0)^2 / (4 * s)) * c₂) volume := by
  -- Work on the product space and use Fubini/Tonelli via Integrable.integral_prod_left.
  let G : SpaceTime × SpaceTime → ℝ := fun p =>
    ‖f p.1‖ * ‖f p.2‖ * c₁ * Real.exp (-(p.1 0 + p.2 0)^2 / (4 * s)) * c₂
  have hG_meas : AEStronglyMeasurable G (volume.prod volume) := by
    have hf : Continuous f := f.continuous
    have h0 : Continuous (fun a : SpaceTime => a 0) :=
      PiLp.continuous_apply 2 (fun _ : Fin STDimension => ℝ) 0
    have hG_cont : Continuous G := by
      simp only [G]
      fun_prop (disch := assumption)
    exact hG_cont.aestronglyMeasurable
  have hG_int : Integrable G (volume.prod volume) := by
    -- Bound by |c₁ c₂| * ‖f p.1‖ * ‖f p.2‖ using exp ≤ 1.
    have h_bound : ∀ p, ‖G p‖ ≤ (|c₁| * |c₂|) * (‖f p.1‖ * ‖f p.2‖) := by
      intro p
      have h_exp_le : Real.exp (-(p.1 0 + p.2 0)^2 / (4 * s)) ≤ 1 := by
        have h_nonneg : 0 ≤ (p.1 0 + p.2 0)^2 / (4 * s) := by
          have hsq : 0 ≤ (p.1 0 + p.2 0)^2 := sq_nonneg _
          have hden : 0 < (4 * s) := by nlinarith [hs]
          exact div_nonneg hsq (le_of_lt hden)
        have hneg' : -(p.1 0 + p.2 0)^2 / (4 * s) = -((p.1 0 + p.2 0)^2 / (4 * s)) := by
          ring
        have hneg : -(p.1 0 + p.2 0)^2 / (4 * s) ≤ 0 := by
          simpa [hneg'] using (neg_nonpos.mpr h_nonneg)
        simpa using (Real.exp_le_exp.mpr hneg)
      have h1 : |Real.exp (-(p.1 0 + p.2 0)^2 / (4 * s))| ≤ 1 := by
        simpa [abs_of_nonneg (Real.exp_nonneg _)] using h_exp_le
      have h_nonneg : 0 ≤ (|c₁| * |c₂|) * (‖f p.1‖ * ‖f p.2‖) := by
        apply mul_nonneg
        · exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
        · exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
      have h2 : (|c₁| * |c₂|) * (‖f p.1‖ * ‖f p.2‖) *
          |Real.exp (-(p.1 0 + p.2 0)^2 / (4 * s))| ≤
          (|c₁| * |c₂|) * (‖f p.1‖ * ‖f p.2‖) * 1 := by
        exact mul_le_mul_of_nonneg_left h1 h_nonneg
      -- Convert to abs bound
      have hnorm : ‖G p‖ = (‖f p.1‖ * ‖f p.2‖) * |c₁| *
          |Real.exp (-(p.1 0 + p.2 0)^2 / (4 * s))| * |c₂| := by
        simp [G, Real.norm_eq_abs, mul_assoc, abs_of_nonneg (Real.exp_nonneg _)]
      have h2' : ((‖f p.1‖ * ‖f p.2‖) * |c₁| *
          |Real.exp (-(p.1 0 + p.2 0)^2 / (4 * s))|) * |c₂| ≤
          ((‖f p.1‖ * ‖f p.2‖) * |c₁| * 1) * |c₂| := by
        have h_nonneg' : 0 ≤ (‖f p.1‖ * ‖f p.2‖) * |c₁| := by
          exact mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (abs_nonneg _)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h_nonneg') (abs_nonneg _)
      have h2'' : ((‖f p.1‖ * ‖f p.2‖) * |c₁| * 1) * |c₂| =
          (|c₁| * |c₂|) * (‖f p.1‖ * ‖f p.2‖) := by
        ring
      have h2_final : (‖f p.1‖ * ‖f p.2‖) * |c₁| *
          |Real.exp (-(p.1 0 + p.2 0)^2 / (4 * s))| * |c₂| ≤
          (|c₁| * |c₂|) * (‖f p.1‖ * ‖f p.2‖) := by
        simpa [mul_assoc] using (h2'.trans_eq h2'')
      simpa [hnorm, mul_assoc] using h2_final
    have h_bound_int : Integrable (fun p : SpaceTime × SpaceTime =>
        (|c₁| * |c₂|) * (‖f p.1‖ * ‖f p.2‖)) (volume.prod volume) := by
      have h_prod : Integrable (fun p : SpaceTime × SpaceTime => ‖f p.1‖ * ‖f p.2‖)
          (volume.prod volume) := hf_int_norm.mul_prod hf_int_norm
      simpa [mul_assoc] using h_prod.const_mul (|c₁| * |c₂|)
    exact Integrable.mono' h_bound_int hG_meas (Eventually.of_forall h_bound)
  -- Conclude by integrating out the second variable.
  have h_int_left : Integrable (fun x : SpaceTime => ∫ y : SpaceTime, G (x, y)) volume :=
    hG_int.integral_prod_left
  simpa [G, mul_assoc, mul_left_comm, mul_comm] using h_int_left

/-- Bound on F(s, k_sp) using linear vanishing of f.

    For f vanishing at t ≤ 0 with |f(x)| ≤ C·x₀, we have:
    |F(s, k_sp)| ≤ C² · (4/3)√π · s^{3/2} · exp(-s(‖k_sp‖² + m²))

    The constant 100 in dominateG provides ample room for the (4/3)√π ≈ 2.36 factor.

    **Proof sketch:**
    1. From `schwartz_vanishing_linear_bound`: |f(x)| ≤ C·x₀ for x₀ > 0
    2. Triangle inequality: |F| ≤ ∫∫ |f(x)||f(y)| · √(π/s) · |exp(...)| dx dy
    3. Key: |exp(-i·...)| = 1, and |f(x)||f(y)| ≤ C²·x₀·y₀
    4. Heat kernel moment integral: ∫∫ x₀·y₀·√(π/s)·exp(-(x₀+y₀)²/(4s)) = (4/3)√π·s^{3/2}
    5. Combine: ≤ C² · (4/3)√π · s^{3/2} · exp(-s(‖k‖²+m²)) < 100 · f_L1² · s^{3/2} · exp(...)

    The detailed calculation is mathematically standard but technically involved.
    See `heat_kernel_moment_integral` for the key integral evaluation.

    **Mathematical justification:**
    The bound uses the linear vanishing property |f(x)| ≤ C·x₀ for x₀ > 0, which combined
    with heat_kernel_moment_integral gives |F| ≤ C² · (4/3)√π · s^{3/2} · exp(-sω²).
    The constant C comes from schwartz_vanishing_linear_bound (derivative bound via MVT).
-/
lemma F_norm_bound_via_linear_vanishing (m : ℝ) [Fact (0 < m)] (f : TestFunctionℂ)
    (hf_supp : ∀ x : SpaceTime, x 0 ≤ 0 → f x = 0) :
    ∃ C_bound : ℝ, 0 < C_bound ∧ ∀ (s : ℝ) (_hs : 0 < s) (k_sp : SpatialCoords),
      let F_val := ∫ x : SpaceTime, ∫ y : SpaceTime,
          (starRingEnd ℂ (f x)) * f y *
            (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
            Complex.exp (-(s : ℂ) * (‖k_sp‖^2 + m^2)) *
            Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y))
      ‖F_val‖ ≤ C_bound * s^(3/2 : ℝ) * Real.exp (-s * (‖k_sp‖^2 + m^2)) := by
  -- Step 1: Get the Fubini bound constant (uses linear vanishing internally)
  obtain ⟨K_fubini, hK_fubini_pos,
    h_fubini_forall⟩ := spacetime_fubini_linear_vanishing_bound f hf_supp
  -- Use the Fubini constant as C_bound
  use K_fubini
  constructor
  · exact hK_fubini_pos
  -- Step 2: For each s > 0 and k_sp, prove the bound
  intro s hs k_sp F_val
  -- Key exponential factor
  let ω_sq := ‖k_sp‖^2 + m^2
  have hω_sq_pos : 0 < ω_sq := by
    have hm : 0 < m := Fact.out
    positivity
  -- Step A: Factor out exp(-s·ω²) from the integral
  -- The integrand has the form: fbar(x)·f(y) · √(π/s) · exp(-t²/(4s)) · exp(-s·ω²) · exp(-i·phase)
  -- Since exp(-s·ω²) is constant in x,y, we can factor it out
  -- Step B: Bound the remaining integral
  -- |∫∫ fbar(x)f(y) · √(π/s) · exp(-t²/(4s)) · exp(-i·phase)| ≤
  -- ∫∫ |f(x)||f(y)| · √(π/s) · exp(-t²/(4s))
  -- (using |exp(-i·phase)| = 1 and |exp(-t²/(4s))| ≤ 1)
  -- Step C: Use linear vanishing: |f(x)| ≤ C_lin · x₀ when x₀ > 0, and f = 0 when x₀ ≤ 0
  -- So |f(x)||f(y)| ≤ C_lin² · x₀ · y₀ · 𝟙_{x₀>0,y₀>0}
  -- Step D: Bound the heat kernel integral
  -- ∫∫ C_lin² · x₀ · y₀ · √(π/s) · exp(-(x₀+y₀)²/(4s)) dx₀ dy₀
  -- = C_lin² · (4/3)√π · s^{3/2}  (by heat_kernel_moment_integral)
  -- < C_lin² · 5 · s^{3/2}  (since (4/3)√π ≈ 2.36 < 5)
  -- The full proof follows this outline. The technical challenge is that SpaceTime = ℝ⁴
  -- while heat_kernel_moment_integral is stated for time coordinates only.
  -- We need to integrate out the spatial coordinates (which are bounded by Schwartz decay).
  -- Estimate: triangle inequality, then the pointwise bound ‖integrand‖ ≤
  -- ‖f x‖·‖f y‖·√(π/s)·exp(-s·ω²) (using |phase|=1, |heat|≤1), then linear vanishing and
  -- heat_kernel_moment_integral give the C_lin²·5·s^{3/2}·exp(-s·ω²) bound.
  -- Key norm bounds for the integrand factors
  have h_sqrt_norm : ‖(Real.sqrt (π / s) : ℂ)‖ = Real.sqrt (π / s) := norm_sqrt_pi_div s
  have h_exp_omega_norm : ‖Complex.exp (-(s : ℂ) * (‖k_sp‖^2 + m^2))‖ =
      Real.exp (-s * (‖k_sp‖^2 + m^2)) := by
    rw [Complex.norm_exp]
    simp only [neg_re, mul_re, Complex.ofReal_re]
    congr 1
    have h_im : (↑‖k_sp‖ ^ 2 + ↑m ^ 2 : ℂ).im = 0 := by simp [sq, Complex.add_im]
    have h_re : (↑‖k_sp‖ ^ 2 + ↑m ^ 2 : ℂ).re = ‖k_sp‖^2 + m^2 := by
      simp only [Complex.add_re, sq, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
    simp only [h_im, h_re, mul_zero, sub_zero]
  -- The L¹ norms of f are finite (Schwartz)
  have hf_int_norm : Integrable (fun x => ‖f x‖) volume := f.integrable.norm
  -- Refined pointwise bound keeping the heat kernel factor (crucial for the s^{3/2} scaling,
  -- via linear vanishing ‖f x‖ ≤ C_lin · x₀ and heat_kernel_moment_integral):
  have h_pointwise_with_heat : ∀ x y : SpaceTime,
      ‖(starRingEnd ℂ (f x)) * f y *
        (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
        Complex.exp (-(s : ℂ) * (‖k_sp‖^2 + m^2)) *
        Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y))‖ ≤
      ‖f x‖ * ‖f y‖ * Real.sqrt (π / s) * Real.exp (-(x 0 + y 0)^2 / (4 * s)) *
        Real.exp (-s * (‖k_sp‖^2 + m^2)) := by
    intro x y
    have h_star : ‖star (f x)‖ = ‖f x‖ := norm_star _
    have h_heat : ‖Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ))‖ =
        Real.exp (-(x 0 + y 0)^2 / (4 * s)) := by
      rw [Complex.norm_exp]; simp only [neg_re, Complex.ofReal_re]; congr 1; ring
    have h_exp3 : ‖Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y))‖ = 1
      :=
      norm_exp_neg_I_mul_real _
    simp only [norm_mul, starRingEnd_apply, h_star, h_sqrt_norm, h_heat, h_exp_omega_norm, h_exp3,
               mul_one, le_refl]
  -- MAIN BOUND using spacetime_fubini_linear_vanishing_bound
  -- The key estimate from spacetime_fubini_linear_vanishing_bound (using K_fubini from earlier)
  have h_fubini_bound := h_fubini_forall s hs
  -- Abbreviate the exponential factor
  let exp_factor := Real.exp (-s * (‖k_sp‖^2 + m^2))
  have hexp_nonneg : 0 ≤ exp_factor := Real.exp_nonneg _
  -- Step 1: Triangle inequality for outer integral
  have step1 : ‖F_val‖ ≤ ∫ x : SpaceTime, ‖∫ y : SpaceTime,
      (starRingEnd ℂ (f x)) * f y *
        (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
        Complex.exp (-(s : ℂ) * (‖k_sp‖^2 + m^2)) *
        Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y))‖ :=
    MeasureTheory.norm_integral_le_integral_norm _
  -- Step 2: For each x, apply triangle inequality to inner integral
  have step2 : ∀ x : SpaceTime, ‖∫ y : SpaceTime,
      (starRingEnd ℂ (f x)) * f y *
        (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
        Complex.exp (-(s : ℂ) * (‖k_sp‖^2 + m^2)) *
        Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y))‖ ≤
      ∫ y : SpaceTime, ‖f x‖ * ‖f y‖ * Real.sqrt (π / s) * Real.exp (-(x 0 + y 0)^2 / (4 * s)) *
        exp_factor := by
    intro x
    refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
    apply MeasureTheory.integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
    · -- Integrability: ‖f x‖ * ‖f a‖ * √(π/s) * exp(-...) * exp_factor
      -- Bounded by (‖f x‖ * √(π/s) * exp_factor) * ‖f a‖ since exp(-...) ≤ 1
      refine Integrable.mono (hf_int_norm.const_mul (‖f x‖ * √(π / s) * exp_factor)) ?_ ?_
      · -- AEStronglyMeasurable
        exact schwartz_heat_product_aestronglymeasurable f x (√(π / s)) exp_factor s hs
      · -- ‖integrand‖ ≤ ‖bound‖
        apply Filter.Eventually.of_forall
        intro a
        simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
                   abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hexp_nonneg]
        have h4s_pos : 0 < 4 * s := by linarith
        have hexp_le : Real.exp (-(x 0 + a 0)^2 / (4 * s)) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          apply div_nonpos_of_nonpos_of_nonneg
          · exact neg_nonpos.mpr (sq_nonneg _)
          · linarith
        calc ‖f x‖ * ‖f a‖ * √(π / s) * |rexp (-(x 0 + a 0)^2 / (4 * s))| * exp_factor
            ≤ ‖f x‖ * ‖f a‖ * √(π / s) * 1 * exp_factor := by
              gcongr; rw [abs_of_nonneg (Real.exp_nonneg _)]; exact hexp_le
          _ = ‖f x‖ * √(π / s) * exp_factor * ‖f a‖ := by ring
    · exact Filter.Eventually.of_forall (fun y => h_pointwise_with_heat x y)
  -- Step 3: Combine steps 1 and 2 to get double integral bound
  have step3 : ‖F_val‖ ≤ ∫ x : SpaceTime, ∫ y : SpaceTime,
      ‖f x‖ * ‖f y‖ * Real.sqrt (π / s) * Real.exp (-(x 0 + y 0)^2 / (4 * s)) * exp_factor := by
    refine le_trans step1 ?_
    apply MeasureTheory.integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
    · -- Integrability
      exact schwartz_iterated_integral_integrable f hf_int_norm (√(π / s)) exp_factor s hs
    · exact Filter.Eventually.of_forall step2
  -- Step 4: Factor out exp_factor using integral_mul_const
  have step4 : ∫ x : SpaceTime, ∫ y : SpaceTime,
      ‖f x‖ * ‖f y‖ * Real.sqrt (π / s) * Real.exp (-(x 0 + y 0)^2 / (4 * s)) * exp_factor =
      (∫ x : SpaceTime, ∫ y : SpaceTime,
        ‖f x‖ * ‖f y‖ * Real.sqrt (π / s) * Real.exp (-(x 0 + y 0)^2 / (4 * s))) * exp_factor := by
    conv_lhs =>
      arg 2; ext x
      rw [MeasureTheory.integral_mul_const]
    rw [MeasureTheory.integral_mul_const]
  -- Step 5: Apply h_fubini_bound and rearrange
  calc ‖F_val‖ ≤ ∫ x : SpaceTime, ∫ y : SpaceTime,
        ‖f x‖ * ‖f y‖ * Real.sqrt (π / s) * Real.exp (-(x 0 + y 0)^2 / (4 * s)) * exp_factor :=
          step3
    _ = (∫ x : SpaceTime, ∫ y : SpaceTime,
          ‖f x‖ * ‖f y‖ * Real.sqrt (π / s) * Real.exp (-(x 0 + y 0)^2 / (4 * s))) * exp_factor :=
            step4
    _ ≤ (K_fubini * s^(3/2 : ℝ)) * exp_factor := by
        apply mul_le_mul_of_nonneg_right h_fubini_bound hexp_nonneg
    _ = K_fubini * s^(3/2 : ℝ) * Real.exp (-s * (‖k_sp‖^2 + m^2)) := by ring

/-- **Fubini swap for s ↔ pbar integrals.**

    Swaps integration order:
    ∫₀^∞ ds ∫_ℝ³ d³pbar F(s, pbar) = ∫_ℝ³ d³pbar ∫₀^∞ ds F(s, pbar)

    where the integrand contains:
    - √(π/s) · exp(-t²/(4s)) from the k₀ Gaussian integral
    - exp(-s(|pbar|² + m²)) from the spatial momentum and mass
    - exp(-ipbar·rbar) phase factor

    **Justification:** Fubini applies because:
    1. The pbar-dependence is Schwartz (Fourier transform of Schwartz test functions)
    2. The s-integrand decays as exp(-s·ω²) where ω² = |pbar|² + m² > 0
    3. Combined integrability on ℝ³ × (0,∞) follows from `Integrable.prod_mul`

    **Note:** This is the most delicate step. Requires splitting the region into
    "small s" (UV, controlling 1/r² singularity) and "large s" (IR, using mass m).

    **Validation:** Reviewed by Gemini 3 Pro - confirmed mathematically valid,
    assuming m > 0 which ensures exponential decay at large s for all k_sp.

    **Key integrability lemma:** Uses `integrable_s_inv_sq_exp_neg_inv_s` to
    handle the s^{-1/2} * exp(-t²/(4s)) term via substitution z = 1/s.
-/
theorem fubini_s_ksp_swap (m : ℝ) [Fact (0 < m)] (f : TestFunctionℂ)
    (hf_supp : ∀ x, x 0 ≤ 0 → f x = 0) :
    ∫ s in Set.Ioi 0, ∫ k_sp : SpatialCoords, ∫ x : SpaceTime, ∫ y : SpaceTime,
      (starRingEnd ℂ (f x)) * f y *
        (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
        Complex.exp (-(s : ℂ) * (‖k_sp‖^2 + m^2)) *
        Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) =
    ∫ k_sp : SpatialCoords, ∫ s in Set.Ioi 0, ∫ x : SpaceTime, ∫ y : SpaceTime,
      (starRingEnd ℂ (f x)) * f y *
        (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
        Complex.exp (-(s : ℂ) * (‖k_sp‖^2 + m^2)) *
        Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) := by
  -- Define the uncurried integrand
  let F : ℝ × SpatialCoords → ℂ := fun ⟨s, k_sp⟩ =>
    ∫ x : SpaceTime, ∫ y : SpaceTime,
      (starRingEnd ℂ (f x)) * f y *
        (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
        Complex.exp (-(s : ℂ) * (‖k_sp‖^2 + m^2)) *
        Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y))
  -- The key integrability: F is integrable on (0,∞) × ℝ³
  have hm : 0 < m := Fact.out
  have hm2 : 0 < m^2 := sq_pos_of_pos hm
  -- Bound function for (s, k_sp): C * s^{-1/2} * exp(-s*m²) * exp(-s*|k|²)
  -- This factorizes as (s^{-1/2} * exp(-s*m²)) × exp(-s*|k|²)
  --
  -- For the s integral: ∫₀^∞ s^{-1/2} exp(-s(|k|² + m²)) ds = √(π/(|k|² + m²))
  -- For the k integral: ∫ exp(-s|k|²) dk = (π/s)^{3/2}
  --
  -- Combined: The integrand ∼ s^{-1/2} exp(-s(|k|² + m²)) |f|₁² is integrable
  -- by Fubini since we can bound the x,y integrals by Schwartz integrability.
  have h_int : Integrable F ((volume.restrict (Set.Ioi 0)).prod volume) := by
    /-
    **Integrability of F on (0,∞) × ℝ³:**

    The integrand F(s, k_sp) involves:
    - Heat kernel factor: √(π/s) · exp(-(x₀+y₀)²/(4s))
    - Mass regularization: exp(-s·(‖k_sp‖² + m²))
    - Schwartz test functions: fbar(x) · f(y)
    - Oscillatory phase: exp(-i·k_sp·(x_sp - y_sp))

    **Bound construction:**
    |F(s, k_sp)| ≤ √(π/s) · exp(-s·m²) · ∫∫ |f(x)||f(y)| · exp(-(x₀+y₀)²/(4s)) dx dy

    **Key observations:**
    1. For f supported on {x₀ > 0}, we have x₀ + y₀ ≥ t_min > 0 on supp(f) × supp(f)
    2. This gives exp(-(x₀+y₀)²/(4s)) ≤ exp(-t_min²/(4s)) uniformly
    3. The Schwartz integrals give ∫∫|f||f| = ‖f‖₁² < ∞

    **Dominating function:**
    G(s, k_sp) = C · s^{-1/2} · exp(-t_min²/(4s)) · exp(-s·m²) · exp(-s·‖k_sp‖²)

    where C = √π · ‖f‖₁².

    **Integrability of G:**
    - s-integral: ∫₀^∞ s^{-1/2} · exp(-t_min²/(4s)) · exp(-s·m²) ds
      This converges at s→0 due to exp(-t_min²/(4s)) → 0 faster than any polynomial,
      and at s→∞ due to exp(-s·m²).
    - k_sp-integral: ∫_{ℝ³} exp(-s·‖k_sp‖²) dk_sp = (π/s)^{3/2}
      Combined with s^{-1/2} gives s^{-2}, still regularized by exp(-t_min²/(4s)).
    -/

    -- Step 1: Extract minimum time separation from support
    -- For f vanishing on {x₀ ≤ 0}, the support of |f|·|f| has x₀ + y₀ > 0
    -- By compactness of Schwartz "effective support", there exists t_min > 0.
    -- (This is the atomic fact about Schwartz functions vanishing at t=0)
    -- Step 2: Define the dominating function using the constant from
    -- F_norm_bound_via_linear_vanishing
    -- Get the constant C_bound from the linear vanishing bound
    obtain ⟨C_bound, hC_pos, h_F_bound⟩ := F_norm_bound_via_linear_vanishing m f hf_supp
    let G := dominateG C_bound m
    -- Note: We omit exp(-t_min²/(4s)) for simplicity; the mass term suffices for large s,
    -- and the full argument needs the UV regulator for small s.
    -- Step 3: Show G is integrable
    have hG_int : Integrable G ((volume.restrict (Set.Ioi 0)).prod volume) :=
      integrable_dominate_G C_bound m
    -- Step 4: Show |F| ≤ G pointwise a.e.
    have hF_le_G : ∀ᵐ p ∂((volume.restrict (Set.Ioi 0)).prod volume), ‖F p‖ ≤ G p := by
      -- On the restricted measure (Ioi 0) × volume, we have s > 0 a.e.
      -- Use Measure.ae_prod_iff_ae_ae: we show for a.e. s, for all k_sp, the bound holds
      rw [Measure.ae_prod_iff_ae_ae]
      · apply (ae_restrict_mem measurableSet_Ioi).mono
        intro s hs
        -- hs : s ∈ Set.Ioi 0, i.e., s > 0
        apply Eventually.of_forall
        intro k_sp
        have hs' : 0 < s := hs
        -- Apply F_norm_bound_via_linear_vanishing with the obtained constant
        have h_bound := h_F_bound s hs' k_sp
        -- dominateG equals C * s^(3/2) * exp(-s*(‖k‖² + m²)) for s > 0
        simpa only [G, dominateG, hs', ↓reduceIte] using h_bound
      · -- Measurability: {p | ‖F p‖ ≤ G p} is measurable
        apply measurableSet_le
        · -- ‖F‖ is measurable
          exact Measurable.norm <| (fubini_s_ksp_integrand_stronglyMeasurable m
            f).integral_prod_right.integral_prod_right.measurable
        · -- G = dominateG C_bound m is measurable
          -- dominateG is a product of measurable functions with an if-statement
          apply Measurable.ite
          · exact measurableSet_lt measurable_const measurable_fst
          · apply Measurable.mul
            · apply Measurable.mul
              · exact measurable_const
              · exact measurable_fst.pow_const _
            · exact (measurable_fst.neg.mul
                ((measurable_snd.norm.pow_const 2).add measurable_const)).exp
          · exact measurable_const
    -- Step 5: Apply Integrable.mono'
    have hF_meas : AEStronglyMeasurable F ((volume.restrict (Set.Ioi 0)).prod volume) := by
      -- F(s, k_sp) = ∫ x, ∫ y, integrand(s, k_sp, x, y)
      -- Use StronglyMeasurable.integral_prod_right twice, with the helper lemma
      apply MeasureTheory.StronglyMeasurable.aestronglyMeasurable
      apply MeasureTheory.StronglyMeasurable.integral_prod_right
      apply MeasureTheory.StronglyMeasurable.integral_prod_right
      exact fubini_s_ksp_integrand_stronglyMeasurable m f
    exact Integrable.mono' hG_int hF_meas hF_le_G
  rw [MeasureTheory.integral_integral_swap h_int]


/-- Schwartz function norm is integrable. -/
lemma schwartz_norm_integrable (f : TestFunctionℂ) :
    MeasureTheory.Integrable (fun x : SpaceTime => ‖f x‖) :=
  (SchwartzMap.integrable f).norm

/-- Product of Schwartz norms is integrable on SpaceTime × SpaceTime. -/
lemma schwartz_norm_prod_integrable (f : TestFunctionℂ) :
    MeasureTheory.Integrable
      (fun p : SpaceTime × SpaceTime => ‖f p.1‖ * ‖f p.2‖)
      (MeasureTheory.volume.prod MeasureTheory.volume) :=
  (schwartz_norm_integrable f).mul_prod (schwartz_norm_integrable f)

/-- Bound function for s_xy_swap. -/
def sXYSwapBound (f : TestFunctionℂ) (m : ℝ) (p : ℝ × SpaceTime × SpaceTime) : ℝ :=
  Real.sqrt (π / p.1) * ‖f p.2.1‖ * ‖f p.2.2‖ * Real.exp (-p.1 * m^2)

lemma s_xy_swap_bound_integrable (f : TestFunctionℂ) (m : ℝ) [Fact (0 < m)] :
    Integrable (sXYSwapBound f m)
      ((volume.restrict (Set.Ioi 0)).prod (volume.prod volume)) := by
  let g_s : ℝ → ℝ := fun s => Real.sqrt π * s ^ (-(1:ℝ)/2) * Real.exp (-m^2 * s)
  let g_xy : SpaceTime × SpaceTime → ℝ := fun p => ‖f p.1‖ * ‖f p.2‖
  -- 1. Integrability of g_s on (0, ∞): ∫₀^∞ √π * s^{-1/2} * exp(-m²s) ds < ∞
  -- This is a Gamma-type integral: Γ(1/2) * (m²)^{-1/2} = √(π/m²)
  have hm : 0 < m := Fact.out
  have hm2 : 0 < m^2 := sq_pos_of_pos hm
  have h_s : Integrable g_s (volume.restrict (Set.Ioi 0)) := by
    -- g_s(s) = √π * (s^{-1/2} * exp(-m² s))
    have h_inner : Integrable (fun s => s ^ (-(1:ℝ)/2) * Real.exp (-m^2 * s)) (volume.restrict
      (Set.Ioi 0)) := by
      have hr : (-1 : ℝ) < -(1:ℝ)/2 := by norm_num
      have hp : (1 : ℝ) ≤ 1 := le_refl 1
      have h := integrableOn_rpow_mul_exp_neg_mul_rpow hr hp hm2
      simp only [Real.rpow_one] at h
      exact h
    convert h_inner.const_mul (Real.sqrt π) using 1
    ext s
    ring
  -- 2. Integrability of g_xy: ∫∫ |f(x)||f(y)| dx dy < ∞
  have h_xy : Integrable g_xy (volume.prod volume) := schwartz_norm_prod_integrable f
  -- 3. Product integrability using Integrable.mul_prod
  have h_prod := h_s.mul_prod h_xy
  -- 4. Convert to sXYSwapBound via AE equality
  apply Integrable.congr h_prod
  -- Need: g_s(s) * g_xy(x,y) = sXYSwapBound f m (s, x, y) a.e.
  filter_upwards with ⟨s, x, y⟩
  dsimp only [sXYSwapBound, g_s, g_xy]
  -- Algebraically: √π * s^{-1/2} * exp(-m²s) * |f x| * |f y| = √(π/s) * |f x| * |f y| * exp(-s*m²)
  by_cases hs : 0 < s
  · -- Key identity: √(π/s) = √π * s^{-1/2} for s > 0
    have h_sqrt : Real.sqrt (π / s) = Real.sqrt π * s ^ (-(1:ℝ)/2) := by
      rw [Real.sqrt_div Real.pi_nonneg, div_eq_mul_inv]
      congr 1
      -- (√s)⁻¹ = s^{-1/2}
      rw [Real.sqrt_eq_rpow]
      rw [← Real.rpow_neg (le_of_lt hs)]
      congr 1
      norm_num
    rw [h_sqrt]
    ring_nf
  · -- For s ≤ 0, both sides are 0 (√ of negative = 0, rpow of nonpositive = 0)
    push Not at hs
    have h_sqrt : Real.sqrt (π / s) = 0 :=
      Real.sqrt_eq_zero'.mpr (div_nonpos_of_nonneg_of_nonpos Real.pi_nonneg hs)
    have h_rpow : s ^ (-(1:ℝ)/2) = 0 := by
      rcases eq_or_lt_of_le hs with rfl | hs'
      · exact Real.zero_rpow (by norm_num : -(1:ℝ)/2 ≠ 0)
      · -- For s < 0, rpow involves cos which vanishes at -π/2
        rw [Real.rpow_def_of_neg hs']
        -- Goal: exp(log s * (-1/2)) * cos(-1/2 * π) = 0
        have hcos : Real.cos (-(1:ℝ)/2 * π) = 0 := by
          have h1 : (-(1:ℝ)/2) * π = -(π/2) := by ring
          rw [h1, Real.cos_neg, Real.cos_pi_div_two]
        rw [hcos, mul_zero]
    rw [h_sqrt, h_rpow]
    ring_nf

private lemma fubini_s_xy_swap_integrable (m : ℝ) [Fact (0 < m)]
    (f : TestFunctionℂ) (k_sp : SpatialCoords) :
    Integrable
      (fun p : ℝ × SpaceTime × SpaceTime =>
        (starRingEnd ℂ (f p.2.1)) * f p.2.2 *
          (Real.sqrt (π / p.1) : ℂ) * Complex.exp (-((-(p.2.1 0) - p.2.2 0)^2 / (4 * p.1) : ℝ)) *
          Complex.exp (-(p.1 : ℂ) * (‖k_sp‖^2 + m^2)) *
          Complex.exp (-Complex.I * spatialDot k_sp (spatialPart p.2.1 - spatialPart p.2.2)))
      ((volume.restrict (Set.Ioi 0)).prod (volume.prod volume)) := by
  have h_bound := s_xy_swap_bound_integrable f m
  apply h_bound.mono'
  · have h_measure : ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))).prod
        ((volume : Measure SpaceTime).prod (volume : Measure SpaceTime)) =
        ((volume : Measure ℝ).prod ((volume : Measure SpaceTime).prod (volume : Measure
            SpaceTime))).restrict
          ((Set.Ioi (0 : ℝ)) ×ˢ Set.univ) := Measure.restrict_prod_eq_prod_univ (Set.Ioi (0 : ℝ))
    rw [h_measure]
    have hf_cont : Continuous f := SchwartzMap.continuous f
    have h1 : ContinuousOn (fun (p : ℝ × SpaceTime × SpaceTime) => (starRingEnd ℂ) (f p.2.1))
        (Set.Ioi 0 ×ˢ Set.univ) := (continuous_star.comp (hf_cont.comp
           continuous_snd.fst)).continuousOn
    have h2 : ContinuousOn (fun (p : ℝ × SpaceTime × SpaceTime) => f p.2.2)
        (Set.Ioi 0 ×ˢ Set.univ) := (hf_cont.comp continuous_snd.snd).continuousOn
    have h3 : ContinuousOn
        (fun (p : ℝ × SpaceTime × SpaceTime) => (Real.sqrt (π / p.1) : ℂ))
        (Set.Ioi 0 ×ˢ Set.univ) := by
      apply ContinuousOn.comp continuous_ofReal.continuousOn _ (Set.mapsTo_univ _ _)
      apply ContinuousOn.sqrt
      apply ContinuousOn.div continuousOn_const continuousOn_fst
      intro ⟨s, _⟩ ⟨hs, _⟩; exact ne_of_gt hs
    have hcoord0_1 : Continuous (fun (p : ℝ × SpaceTime × SpaceTime) => p.2.1 0) :=
      (PiLp.continuous_apply 2 (fun _ : Fin STDimension => ℝ) 0).comp continuous_snd.fst
    have hcoord0_2 : Continuous (fun (p : ℝ × SpaceTime × SpaceTime) => p.2.2 0) :=
      (PiLp.continuous_apply 2 (fun _ : Fin STDimension => ℝ) 0).comp continuous_snd.snd
    have h4 : ContinuousOn (fun (p : ℝ × SpaceTime × SpaceTime) =>
        Complex.exp (-((-(p.2.1 0) - p.2.2 0)^2 / (4 * p.1) : ℝ))) (Set.Ioi 0 ×ˢ Set.univ) := by
      apply Complex.continuous_exp.comp_continuousOn
      apply ContinuousOn.neg
      apply ContinuousOn.comp continuous_ofReal.continuousOn _ (Set.mapsTo_univ _ _)
      apply ContinuousOn.div
      · exact ((hcoord0_1.neg.sub hcoord0_2).pow 2).continuousOn
      · exact (continuous_const.mul continuous_fst).continuousOn
      · intro ⟨s, _⟩ ⟨hs, _⟩
        simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
        exact ne_of_gt hs
    have h5 : ContinuousOn (fun (p : ℝ × SpaceTime × SpaceTime) =>
        Complex.exp (-(p.1 : ℂ) * (‖k_sp‖^2 + m^2))) (Set.Ioi 0 ×ˢ Set.univ) := by
      apply Complex.continuous_exp.comp_continuousOn
      apply ContinuousOn.mul
      · exact (continuous_ofReal.comp continuous_fst).neg.continuousOn
      · exact continuousOn_const
    have h6 : ContinuousOn (fun (p : ℝ × SpaceTime × SpaceTime) =>
        Complex.exp (-Complex.I * spatialDot k_sp (spatialPart p.2.1 - spatialPart p.2.2)))
        (Set.Ioi 0 ×ˢ Set.univ) := by
      apply Complex.continuous_exp.comp_continuousOn
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.comp continuous_ofReal.continuousOn _ (Set.mapsTo_univ _ _)
      unfold spatialDot
      have h_spatialPart_cont : Continuous spatialPart := continuous_spatialPart
      have h_sum : Continuous (fun p : ℝ × SpaceTime × SpaceTime =>
          ∑ i, k_sp i * (spatialPart p.2.1 - spatialPart p.2.2) i) := by
        apply continuous_finsetSum
        intro i _
        have hv_i : Continuous (fun (p : ℝ × SpaceTime × SpaceTime) =>
            (spatialPart p.2.1 - spatialPart p.2.2) i) :=
          (PiLp.continuous_apply 2 (fun _ : Fin (STDimension - 1) => ℝ) i).comp
            ((h_spatialPart_cont.comp continuous_snd.fst).sub
             (h_spatialPart_cont.comp continuous_snd.snd))
        exact continuous_const.mul hv_i
      exact h_sum.continuousOn
    have h_cont := ((((h1.mul h2).mul h3).mul h4).mul h5).mul h6
    have h_meas : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (SpaceTime × SpaceTime))) :=
      measurableSet_Ioi.prod MeasurableSet.univ
    exact h_cont.aestronglyMeasurable h_meas
  · have h_ae : ∀ᵐ p : ℝ × SpaceTime × SpaceTime ∂(volume.restrict (Set.Ioi 0)).prod (volume.prod
      volume),
      0 < p.1 := by
      rw [Filter.eventually_iff, MeasureTheory.mem_ae_iff]
      have h_compl : ({p : ℝ × SpaceTime × SpaceTime | 0 < p.1})ᶜ =
          Prod.fst ⁻¹' Set.Iic 0 := by
        ext p; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt, Set.mem_preimage,
          Set.mem_Iic]
      rw [h_compl]
      have h_prod : (Prod.fst ⁻¹' Set.Iic (0 : ℝ) : Set (ℝ × SpaceTime × SpaceTime)) =
          Set.Iic 0 ×ˢ Set.univ := by
        ext ⟨s, xy⟩
        simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_prod, Set.mem_univ, and_true]
      rw [h_prod, MeasureTheory.Measure.prod_prod]
      simp only [MeasureTheory.Measure.restrict_apply measurableSet_Iic,
        Set.Iic_inter_Ioi, Set.Ioc_self, MeasureTheory.measure_empty, zero_mul]
    filter_upwards [h_ae] with ⟨s, x, y⟩ hs
    dsimp only [sXYSwapBound]
    refine (cexp6_norm_le_mass f s m hs.le x y k_sp).trans_eq ?_
    ring

/-- **Fubini swap for s ↔ (x,y) integrals (for fixed k_sp).**

    For fixed k_sp, swaps integration order:
    ∫₀^∞ ds ∫_x ∫_y F(s,x,y) = ∫_x ∫_y ∫₀^∞ ds F(s,x,y)

    **Proof:** Uses `MeasureTheory.integral_integral_swap` with
    integrability on `(Set.Ioi 0) × SpaceTime × SpaceTime`.
    The bound function is `s^{-1/2} * exp(-s*m^2) * |f(x)| * |f(y)|`.
-/
theorem fubini_s_xy_swap (m : ℝ) [Fact (0 < m)] (f : TestFunctionℂ) (k_sp : SpatialCoords) :
    ∫ s in Set.Ioi 0, ∫ x : SpaceTime, ∫ y : SpaceTime,
      (starRingEnd ℂ (f x)) * f y *
        (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
        Complex.exp (-(s : ℂ) * (‖k_sp‖^2 + m^2)) *
        Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) =
    ∫ x : SpaceTime, ∫ y : SpaceTime, ∫ s in Set.Ioi 0,
      (starRingEnd ℂ (f x)) * f y *
        (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
        Complex.exp (-(s : ℂ) * (‖k_sp‖^2 + m^2)) *
        Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) := by
  -- Define the full integrand
  let F : ℝ × SpaceTime × SpaceTime → ℂ := fun ⟨s, x, y⟩ =>
    (starRingEnd ℂ (f x)) * f y *
      (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
      Complex.exp (-(s : ℂ) * (‖k_sp‖^2 + m^2)) *
      Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y))
  have h_int : Integrable F ((volume.restrict (Set.Ioi 0)).prod (volume.prod volume)) := by
    simpa [F] using fubini_s_xy_swap_integrable m f k_sp
  -- The goal is to swap s with (x, y).
  -- h_int gives integrability on the product (Ioi 0) × (SpaceTime × SpaceTime)
  -- Step 1: Rewrite LHS and RHS to use product integrals
  -- LHS: ∫_s (∫_x (∫_y F)) = ∫_s (∫_{xy} F) by integral_prod on inner
  -- RHS: ∫_x (∫_y (∫_s F)) = ∫_{xy} (∫_s F) by integral_prod on outer
  -- Step 2: Apply integral_integral_swap to swap s ↔ xy
  -- ∫_s (∫_{xy} F(s, xy)) = ∫_{xy} (∫_s F(s, xy))
  -- The difficulty is that we have nested integrals ∫_x ∫_y, not a single product integral.
  -- However, for sigma-finite measures, we can use transitivity through the product.
  -- Direct approach: Use the fact that for sigma-finite measures,
  -- ∫_x ∫_y ∫_z f = ∫_z ∫_x ∫_y f when f is integrable on the triple product.
  -- This follows from two applications of Fubini.
  -- By Fubini on (s, (x,y)):  ∫_s ∫_{(x,y)} F = ∫_{(x,y)} ∫_s F
  -- The nested ∫_x ∫_y equals ∫_{(x,y)} by integral_prod
  calc ∫ s in Set.Ioi 0, ∫ x : SpaceTime, ∫ y : SpaceTime, F (s, x, y)
      = ∫ s in Set.Ioi 0, ∫ xy : SpaceTime × SpaceTime, F (s, xy.1, xy.2) := by
          congr 1 with s
          -- ∫_x ∫_y g(x,y) = ∫_{xy} g(xy.1, xy.2) by integral_prod
          symm
          have h_int_s : Integrable (fun xy : SpaceTime × SpaceTime => F (s, xy.1, xy.2))
              (volume.prod volume) := by
            -- For fixed s, F(s,x,y) is bounded by C(s) * |f(x)| * |f(y)|
            -- where C(s) = √(π/s) * exp(-s*m²) (assuming s > 0)
            by_cases hs : 0 < s
            · -- When s > 0, the integrand is a product of bounded terms × Schwartz
              have h_bound : Integrable (fun xy : SpaceTime × SpaceTime =>
                  Real.sqrt (π / s) * ‖f xy.1‖ * ‖f xy.2‖ * Real.exp (-s * m^2))
                  (volume.prod volume) := by
                have h_prod := schwartz_norm_prod_integrable f
                have h1 := h_prod.const_mul (Real.sqrt (π / s) * Real.exp (-s * m^2))
                convert h1 using 1
                ext ⟨x, y⟩; ring
              apply h_bound.mono'
              · -- AEStronglyMeasurable of F(s, ·, ·)
                have hf_cont : Continuous f := SchwartzMap.continuous f
                have h_spatialPart_cont : Continuous spatialPart := continuous_spatialPart
                have h1 : Continuous (fun (xy : SpaceTime × SpaceTime) => (starRingEnd ℂ) (f xy.1))
                  :=
                  continuous_star.comp (hf_cont.comp continuous_fst)
                have h2 : Continuous (fun (xy : SpaceTime × SpaceTime) => f xy.2) :=
                  hf_cont.comp continuous_snd
                have h3 : Continuous (fun (_ : SpaceTime × SpaceTime) => (Real.sqrt (π / s) : ℂ)) :=
                  continuous_const
                have hcoord0_1 : Continuous (fun (xy : SpaceTime × SpaceTime) => xy.1 0) :=
                  (PiLp.continuous_apply 2 (fun _ : Fin STDimension => ℝ) 0).comp continuous_fst
                have hcoord0_2 : Continuous (fun (xy : SpaceTime × SpaceTime) => xy.2 0) :=
                  (PiLp.continuous_apply 2 (fun _ : Fin STDimension => ℝ) 0).comp continuous_snd
                have h4 : Continuous (fun (xy : SpaceTime × SpaceTime) =>
                    Complex.exp (-((-(xy.1 0) - xy.2 0)^2 / (4 * s) : ℝ))) := by
                  apply Complex.continuous_exp.comp
                  apply Continuous.neg
                  apply continuous_ofReal.comp
                  apply Continuous.div_const
                  exact (hcoord0_1.neg.sub hcoord0_2).pow 2
                have h5 : Continuous (fun (_ : SpaceTime × SpaceTime) =>
                    Complex.exp (-(s : ℂ) * (‖k_sp‖^2 + m^2))) := continuous_const
                have h6 : Continuous (fun (xy : SpaceTime × SpaceTime) =>
                    Complex.exp (-Complex.I * spatialDot k_sp (spatialPart xy.1 - spatialPart
                      xy.2))) := by
                  apply Complex.continuous_exp.comp
                  apply Continuous.mul continuous_const
                  apply continuous_ofReal.comp
                  unfold spatialDot
                  apply continuous_finsetSum
                  intro i _
                  have hv_i : Continuous (fun (xy : SpaceTime × SpaceTime) =>
                      (spatialPart xy.1 - spatialPart xy.2) i) :=
                    (PiLp.continuous_apply 2 (fun _ : Fin (STDimension - 1) => ℝ) i).comp
                      ((h_spatialPart_cont.comp continuous_fst).sub
                       (h_spatialPart_cont.comp continuous_snd))
                  exact continuous_const.mul hv_i
                exact ((((h1.mul h2).mul h3).mul h4).mul h5).mul h6 |>.aestronglyMeasurable
              · -- Norm bound
                filter_upwards with ⟨x, y⟩
                dsimp only [F]
                exact (cexp6_norm_le_mass f s m hs.le x y k_sp).trans_eq (by ring)
            · -- When s ≤ 0, √(π/s) = 0 (sqrt of non-positive is 0), so F(s,x,y) = 0
              simp only [not_lt] at hs
              have h_sqrt_zero : Real.sqrt (π / s) = 0 := by
                apply Real.sqrt_eq_zero'.mpr
                exact div_nonpos_of_nonneg_of_nonpos Real.pi_nonneg hs
              have h_F_zero : ∀ xy : SpaceTime × SpaceTime, F (s, xy.1, xy.2) = 0 := by
                intro ⟨x, y⟩
                simp only [F, h_sqrt_zero, Complex.ofReal_zero, mul_zero, zero_mul]
              simp_rw [h_F_zero]
              exact integrable_zero (SpaceTime × SpaceTime) ℂ (volume.prod volume)
          exact MeasureTheory.integral_prod _ h_int_s
    _ = ∫ xy : SpaceTime × SpaceTime, ∫ s in Set.Ioi 0, F (s, xy.1, xy.2) := by
          exact MeasureTheory.integral_integral_swap h_int
    _ = ∫ x : SpaceTime, ∫ y : SpaceTime, ∫ s in Set.Ioi 0, F (s, x, y) := by
          -- ∫_{xy} g(xy) = ∫_x ∫_y g(x,y) by integral_prod
          have h_int_xy : Integrable (fun xy : SpaceTime × SpaceTime =>
              ∫ s in Set.Ioi 0, F (s, xy.1, xy.2)) (volume.prod volume) := by
            -- From h_int : Integrable F ((volume.restrict (Ioi 0)).prod (volume.prod volume))
            -- Integrable.integral_prod_right gives integrability of ∫ (second) ... on (first)
            -- Here the product is s × (x,y), so integral_prod_right gives integrability
            -- of (fun (x,y) => ∫ s, F(s,x,y)) on volume.prod volume
            exact h_int.integral_prod_right
          exact MeasureTheory.integral_prod _ h_int_xy
/-! ## Fubini Helper Lemmas

These lemmas establish the integrability needed for Fubini swaps in the
reflection positivity proof. The key observation is that:

1. Schwartz functions are L¹: ∫|f(x)| dx < ∞
2. Gaussians are L¹: ∫ exp(-s‖k‖²) dk = (π/s)^{n/2}
3. Products of L¹ functions on independent spaces are L¹ on the product

The common bound for all Fubini swaps is:
  |integrand| ≤ |f(x)| |f(y)| × C(s) × exp(-s‖k_sp‖²)
which factors and is therefore integrable on the product space.
-/

/-- The Gaussian exp(-s‖k‖²) is integrable over SpatialCoords for s > 0. -/
lemma gaussian_integrable_spatialCoords (s : ℝ) (hs : 0 < s) :
    MeasureTheory.Integrable (fun k_sp : SpatialCoords => Real.exp (-s * ‖k_sp‖^2)) := by
  have hs' : 0 < (s : ℂ).re := by simp [hs]
  -- Use Mathlib's Gaussian integrability (with c=0, w=0)
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := SpatialCoords) hs' 0 0
  -- Simplify the function: exp(-s‖k‖² + 0 * inner 0 k) = exp(-s‖k‖²)
  simp only [zero_mul, add_zero, inner_zero_left, Complex.ofReal_zero] at h
  -- Now h : Integrable (fun v => exp(-(s:ℂ) * ‖v‖²))
  -- Convert complex exponential to real: exp(-(s:ℂ) * ‖v‖²) for real s is real
  have h_eq : (fun k_sp : SpatialCoords => Complex.exp (-(s : ℂ) * ‖k_sp‖^2)) =
      (fun k_sp => (Real.exp (-s * ‖k_sp‖^2) : ℂ)) := by
    ext k_sp
    -- Use Complex.ofReal_exp: (Real.exp x : ℂ) = Complex.exp (x : ℂ)
    -- We need to show cexp(-(s:ℂ) * ↑‖k‖²) = (rexp(-s * ‖k‖²) : ℂ)
    -- The RHS = cexp(↑(-s * ‖k‖²)) by Complex.ofReal_exp
    -- And ↑(-s * ‖k‖²) = -(s:ℂ) * ↑‖k‖² by push_cast
    simp only [Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_pow]
  rw [h_eq] at h
  -- Integrable (ofReal ∘ g) implies Integrable g via .re since re(ofReal x) = x
  exact h.re

/-- **Key Lemma**: The integrand for fubini_ksp_xy_swap is absolutely integrable.

    The bound |f(x)| |f(y)| exp(-s‖k_sp‖²) is integrable on
    SpatialCoords × SpaceTime × SpaceTime because:
    1. ∫_{k_sp} exp(-s‖k_sp‖²) dk_sp = (π/s)^{3/2} < ∞
    2. ∫∫_{x,y} |f(x)| |f(y)| dx dy = ‖f‖₁² < ∞
    3. The product factorizes on independent spaces
-/
lemma fubini_ksp_xy_integrand_integrable (s : ℝ) (hs : 0 < s) (f : TestFunctionℂ) :
    MeasureTheory.Integrable
      (fun p : SpatialCoords × SpaceTime × SpaceTime =>
        ‖f p.2.1‖ * ‖f p.2.2‖ * Real.exp (-s * ‖p.1‖^2))
      (MeasureTheory.volume.prod (MeasureTheory.volume.prod MeasureTheory.volume)) := by
  -- Factor the integrand
  have h_gauss : MeasureTheory.Integrable
      (fun k_sp : SpatialCoords => Real.exp (-s * ‖k_sp‖^2)) := gaussian_integrable_spatialCoords s
         hs
  have h_schwartz : MeasureTheory.Integrable
      (fun p : SpaceTime × SpaceTime => ‖f p.1‖ * ‖f p.2‖)
      (MeasureTheory.volume.prod MeasureTheory.volume) := schwartz_norm_prod_integrable f
  -- Combine using Integrable.mul_prod
  have h_prod := h_gauss.mul_prod h_schwartz
  -- Rearrange to match our target form
  convert h_prod using 1
  ext ⟨k_sp, x, y⟩
  ring

/-- The full Fubini integrand is absolutely integrable on SpatialCoords × SpaceTime × SpaceTime.

    The integrand is:
      fbar(x) · f(y) · √(π/s) · exp(-t²/4s) · exp(-s‖k_sp‖²) · exp(-ik·r)

    Bound: |integrand| ≤ |f(x)| · |f(y)| · √(π/s) · 1 · exp(-s‖k_sp‖²) · 1
         = √(π/s) · |f(x)| · |f(y)| · exp(-s‖k_sp‖²)

    This is a constant multiple of `fubini_ksp_xy_integrand_integrable`.

    **Proof sketch:** Apply `Integrable.mono'` with the bound function
    √(π/s) * ‖f(x)‖ * ‖f(y)‖ * exp(-s‖k_sp‖²), which is integrable by
    `fubini_ksp_xy_integrand_integrable`. The norm bounds follow from:
    - |starRingEnd ℂ (f x)| = |f x|
    - |ofReal (√(π/s))| = √(π/s) (non-negative)
    - |exp(negative real)| ≤ 1
    - |exp(pure imaginary)| = 1
-/
lemma fubini_ksp_xy_full_integrand_integrable (s : ℝ) (hs : 0 < s) (f : TestFunctionℂ) :
    MeasureTheory.Integrable
      (fun p : SpatialCoords × SpaceTime × SpaceTime =>
        (starRingEnd ℂ (f p.2.1)) * f p.2.2 *
          (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(p.2.1 0) - p.2.2 0)^2 / (4 * s) : ℝ)) *
          Complex.exp (-(s : ℂ) * ‖p.1‖^2) *
          Complex.exp (-Complex.I * spatialDot p.1 (spatialPart p.2.1 - spatialPart p.2.2)))
      (MeasureTheory.volume.prod (MeasureTheory.volume.prod MeasureTheory.volume)) := by
  -- The bound √(π/s) * |f(x)| * |f(y)| * exp(-s‖k_sp‖²) is integrable
  have h_bound_integrable := (fubini_ksp_xy_integrand_integrable s hs f).const_mul (Real.sqrt (π /
    s))
  -- Apply Integrable.mono' with norm bounds
  apply MeasureTheory.Integrable.mono' h_bound_integrable
  · -- AEStronglyMeasurable: product of continuous functions on finite-dim spaces
    -- The integrand is Schwartz × const × exp(real) × exp(real) × exp(pure imaginary)
    -- Each factor is continuous, hence the whole product is continuous
    have hf_cont : Continuous f := SchwartzMap.continuous f
    have h1 : Continuous (fun (p : SpatialCoords × SpaceTime × SpaceTime) => (starRingEnd ℂ) (f
      p.2.1)) :=
      continuous_star.comp (hf_cont.comp continuous_snd.fst)
    have h2 : Continuous (fun (p : SpatialCoords × SpaceTime × SpaceTime) => f p.2.2) :=
      hf_cont.comp continuous_snd.snd
    have h3 : Continuous (fun (_ : SpatialCoords × SpaceTime × SpaceTime) => (Real.sqrt (π / s) :
      ℂ)) :=
      continuous_const
    -- Continuous coordinate access for EuclideanSpace (which is PiLp 2)
    have hcoord0_1 : Continuous (fun (p : SpatialCoords × SpaceTime × SpaceTime) => p.2.1 0) :=
      (PiLp.continuous_apply 2 (fun _ : Fin STDimension => ℝ) 0).comp continuous_snd.fst
    have hcoord0_2 : Continuous (fun (p : SpatialCoords × SpaceTime × SpaceTime) => p.2.2 0) :=
      (PiLp.continuous_apply 2 (fun _ : Fin STDimension => ℝ) 0).comp continuous_snd.snd
    have h4 : Continuous (fun (p : SpatialCoords × SpaceTime × SpaceTime) =>
        Complex.exp (-((-(p.2.1 0) - p.2.2 0)^2 / (4 * s) : ℝ))) := by
      apply Complex.continuous_exp.comp
      apply Continuous.neg
      apply continuous_ofReal.comp
      apply Continuous.div_const
      apply Continuous.pow
      exact hcoord0_1.neg.sub hcoord0_2
    have h5 : Continuous (fun (p : SpatialCoords × SpaceTime × SpaceTime) =>
        Complex.exp (-(s : ℂ) * ‖p.1‖^2)) := by
      apply Complex.continuous_exp.comp
      apply Continuous.mul continuous_const
      apply Continuous.pow
      exact continuous_ofReal.comp (continuous_norm.comp continuous_fst)
    have h6 : Continuous (fun (p : SpatialCoords × SpaceTime × SpaceTime) =>
        Complex.exp (-Complex.I * spatialDot p.1 (spatialPart p.2.1 - spatialPart p.2.2))) := by
      apply Complex.continuous_exp.comp
      apply Continuous.mul continuous_const
      apply continuous_ofReal.comp
      -- spatialDot k_sp v = Σ i, k_sp i * v i is continuous in both arguments
      unfold spatialDot
      apply continuous_finsetSum
      intro i _
      have hk_i : Continuous (fun (p : SpatialCoords × SpaceTime × SpaceTime) => p.1 i) :=
        (PiLp.continuous_apply 2 (fun _ : Fin (STDimension - 1) => ℝ) i).comp continuous_fst
      have hv_i : Continuous (fun (p : SpatialCoords × SpaceTime × SpaceTime) =>
          (spatialPart p.2.1 - spatialPart p.2.2) i) :=
        (PiLp.continuous_apply 2 (fun _ : Fin (STDimension - 1) => ℝ) i).comp
          (continuous_spatialPart.comp continuous_snd.fst |>.sub
           (continuous_spatialPart.comp continuous_snd.snd))
      exact hk_i.mul hv_i
    exact ((((h1.mul h2).mul h3).mul h4).mul h5).mul h6 |>.aestronglyMeasurable
  · -- The norm bound: |F| ≤ √(π/s) · |f x| · |f y| · exp(-s‖k_sp‖²)
    filter_upwards with ⟨k_sp, x, y⟩
    exact (cexp6_norm_le_ksp f s hs.le x y k_sp).trans_eq (by ring)

private lemma fubini_ksp_xy_inner_integrable (s : ℝ) (hs : 0 < s)
    (f : TestFunctionℂ) (x : SpaceTime) :
    MeasureTheory.Integrable
      (fun p : SpaceTime × SpatialCoords =>
        (starRingEnd ℂ (f x)) * f p.1 *
          (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - p.1 0)^2 / (4 * s) : ℝ)) *
          Complex.exp (-(s : ℂ) * ‖p.2‖^2) *
          Complex.exp (-Complex.I * spatialDot p.2 (spatialPart x - spatialPart p.1)))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  have h_bound : MeasureTheory.Integrable
      (fun p : SpaceTime × SpatialCoords => ‖f x‖ * Real.sqrt (π / s) * ‖f p.1‖ *
        Real.exp (-s * ‖p.2‖^2))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    have h1 : MeasureTheory.Integrable (fun y : SpaceTime => ‖f y‖) := schwartz_norm_integrable f
    have h2 : MeasureTheory.Integrable (fun k : SpatialCoords => Real.exp (-s * ‖k‖^2)) :=
      gaussian_integrable_spatialCoords s hs
    convert (h1.mul_prod h2).const_mul (‖f x‖ * Real.sqrt (π / s)) using 1
    ext ⟨y, k⟩
    ring
  apply MeasureTheory.Integrable.mono' h_bound
  · have hf_cont : Continuous f := SchwartzMap.continuous f
    have hcoord : Continuous (fun (p : SpaceTime × SpatialCoords) => p.1 0) :=
      (PiLp.continuous_apply 2 (fun _ : Fin STDimension => ℝ) 0).comp continuous_fst
    have h_cont : Continuous (fun p : SpaceTime × SpatialCoords =>
        (starRingEnd ℂ (f x)) * f p.1 *
          (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - p.1 0)^2 / (4 * s) : ℝ)) *
          Complex.exp (-(s : ℂ) * ‖p.2‖^2) *
          Complex.exp (-Complex.I * spatialDot p.2 (spatialPart x - spatialPart p.1))) := by
      apply Continuous.mul
      · apply Continuous.mul
        · apply Continuous.mul
          · apply Continuous.mul
            · apply Continuous.mul continuous_const (hf_cont.comp continuous_fst)
            · exact continuous_const
          · apply Complex.continuous_exp.comp
            apply Continuous.neg
            apply continuous_ofReal.comp
            apply Continuous.div_const
            apply Continuous.pow
            exact continuous_const.sub hcoord
        · apply Complex.continuous_exp.comp
          apply Continuous.mul continuous_const
          apply Continuous.pow
          exact continuous_ofReal.comp (continuous_norm.comp continuous_snd)
      · apply Complex.continuous_exp.comp
        apply Continuous.mul continuous_const
        apply continuous_ofReal.comp
        unfold spatialDot
        apply continuous_finsetSum
        intro i _
        have hk_i : Continuous (fun (p : SpaceTime × SpatialCoords) => p.2 i) :=
          (PiLp.continuous_apply 2 (fun _ : Fin (STDimension - 1) => ℝ) i).comp continuous_snd
        have hv_i : Continuous (fun (p : SpaceTime × SpatialCoords) => (spatialPart x -
          spatialPart p.1) i) :=
          (PiLp.continuous_apply 2 (fun _ : Fin (STDimension - 1) => ℝ) i).comp
            (continuous_const.sub (continuous_spatialPart.comp continuous_fst))
        exact hk_i.mul hv_i
    exact h_cont.aestronglyMeasurable
  · filter_upwards with ⟨y, k_sp⟩
    exact (cexp6_norm_le_ksp f s hs.le x y k_sp).trans_eq (by ring)

/-- **Fubini swap for k_sp ↔ (x,y) integrals.**

    For fixed s > 0, swaps integration order:
    ∫_x ∫_y (... * ∫_{k_sp} F) = ∫_{k_sp} ∫_x ∫_y (... * F)

    This moves the spatial momentum integral k_sp from inside the spacetime
    integrals (x,y) to outside them.

    **Proof:** Two steps:
    1. Pull the k_sp integral out: A(x,y) * ∫_{k_sp} B = ∫_{k_sp} A(x,y) * B
    2. Apply Fubini (integral_integral_swap) to swap x,y,k_sp to k_sp,x,y
-/
theorem fubini_ksp_xy_swap (s : ℝ) (hs : 0 < s) (f : TestFunctionℂ) :
    ∫ x : SpaceTime, ∫ y : SpaceTime,
      (starRingEnd ℂ (f x)) * f y *
        (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
        ∫ k_sp : SpatialCoords,
          Complex.exp (-(s : ℂ) * ‖k_sp‖^2) *
          Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) =
    ∫ k_sp : SpatialCoords, ∫ x : SpaceTime, ∫ y : SpaceTime,
      (starRingEnd ℂ (f x)) * f y *
        (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
        Complex.exp (-(s : ℂ) * ‖k_sp‖^2) *
        Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) := by
  -- Step 1: Pull the k_sp integral out of the product
  -- A(x,y) * ∫ B(k_sp, x, y) = ∫ A(x,y) * B(k_sp, x, y) by integral_const_mul (reversed)
  -- where A(x,y) = conj(f x) * f y * √(π/s) * exp(-t²/4s) is k_sp-independent
  have h_pull : ∀ x y : SpaceTime,
      (starRingEnd ℂ (f x)) * f y *
        (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
        ∫ k_sp : SpatialCoords,
          Complex.exp (-(s : ℂ) * ‖k_sp‖^2) *
          Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) =
      ∫ k_sp : SpatialCoords,
        (starRingEnd ℂ (f x)) * f y *
          (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
          Complex.exp (-(s : ℂ) * ‖k_sp‖^2) *
          Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) := by
    intro x y
    have : ∀ r : ℂ, ∀ g : SpatialCoords → ℂ,
        r * ∫ a, g a = ∫ a, r * g a :=
      fun r g => (MeasureTheory.integral_const_mul r g).symm
    rw [this]
    congr 1
    ext k_sp
    ring
  -- Rewrite LHS using h_pull
  simp_rw [h_pull]
  -- Now we have ∫_x ∫_y ∫_{k_sp} F(x,y,k_sp). Apply Fubini twice to get ∫_{k_sp} ∫_x ∫_y F.
  --
  -- The Fubini swap uses integral_integral_swap twice:
  -- 1. For each x, swap (y, k_sp) to (k_sp, y)
  -- 2. Swap (x, k_sp) to (k_sp, x)
  --
  -- Step 1: Swap inner (y, k_sp) for each fixed x
  have h_inner : ∀ x : SpaceTime, MeasureTheory.Integrable
      (fun p : SpaceTime × SpatialCoords =>
        (starRingEnd ℂ (f x)) * f p.1 *
          (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - p.1 0)^2 / (4 * s) : ℝ)) *
          Complex.exp (-(s : ℂ) * ‖p.2‖^2) *
          Complex.exp (-Complex.I * spatialDot p.2 (spatialPart x - spatialPart p.1)))
      (MeasureTheory.volume.prod MeasureTheory.volume) :=
    fun x => fubini_ksp_xy_inner_integrable s hs f x
  have h1 : ∀ x, ∫ y, ∫ k_sp,
      (starRingEnd ℂ (f x)) * f y *
        (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
        Complex.exp (-(s : ℂ) * ‖k_sp‖^2) *
        Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) =
      ∫ k_sp, ∫ y,
        (starRingEnd ℂ (f x)) * f y *
          (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
          Complex.exp (-(s : ℂ) * ‖k_sp‖^2) *
          Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) := fun x => by
    exact MeasureTheory.integral_integral_swap (h_inner x)
  conv_lhs => arg 2; ext x; rw [h1 x]
  -- Step 2: Swap (x, k_sp)
  -- Define the full integrand on ((x, k), y)
  let F : (SpaceTime × SpatialCoords) × SpaceTime → ℂ := fun ⟨⟨x, k⟩, y⟩ =>
    (starRingEnd ℂ (f x)) * f y *
      (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
      Complex.exp (-(s : ℂ) * ‖k‖^2) *
      Complex.exp (-Complex.I * spatialDot k (spatialPart x - spatialPart y))
  -- Prove F is integrable on ((x, k), y)
  have h_F_integrable : MeasureTheory.Integrable F
      ((MeasureTheory.volume.prod MeasureTheory.volume).prod MeasureTheory.volume) := by
    -- Bound: |F((x,k),y)| ≤ √(π/s) * ‖f(x)‖ * ‖f(y)‖ * exp(-s‖k‖²)
    have h_bound : MeasureTheory.Integrable
        (fun (p : (SpaceTime × SpatialCoords) × SpaceTime) =>
          Real.sqrt (π / s) * ‖f p.1.1‖ * ‖f p.2‖ * Real.exp (-s * ‖p.1.2‖^2))
        ((MeasureTheory.volume.prod MeasureTheory.volume).prod MeasureTheory.volume) := by
      have h1 : MeasureTheory.Integrable (fun x : SpaceTime => ‖f x‖) := schwartz_norm_integrable f
      have h2 : MeasureTheory.Integrable (fun k : SpatialCoords => Real.exp (-s * ‖k‖^2)) :=
        gaussian_integrable_spatialCoords s hs
      -- The bound is √(π/s) * ‖f(x)‖ * exp(-s‖k‖²) * ‖f(y)‖
      -- = (√(π/s) * ‖f(x)‖ * exp(-s‖k‖²)) * ‖f(y)‖
      -- Integrable on (x,k) × y
      have h_xk : MeasureTheory.Integrable
          (fun p : SpaceTime × SpatialCoords => Real.sqrt (π / s) * ‖f p.1‖ * Real.exp (-s *
             ‖p.2‖^2))
          (MeasureTheory.volume.prod MeasureTheory.volume) := by
        convert ((h1.mul_prod h2).const_mul (Real.sqrt (π / s))) using 1
        ext ⟨x, k⟩; ring
      convert h_xk.mul_prod h1 using 1
      ext ⟨⟨x, k⟩, y⟩; ring
    apply MeasureTheory.Integrable.mono' h_bound
    · -- AEStronglyMeasurable of F
      -- Show the explicit form of F via simp only
      simp only [F]
      have hf_cont : Continuous f := SchwartzMap.continuous f
      have h_cont : Continuous (fun p : (SpaceTime × SpatialCoords) × SpaceTime =>
          (starRingEnd ℂ (f p.1.1)) * f p.2 *
            (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(p.1.1 0) - p.2 0)^2 / (4 * s) : ℝ)) *
            Complex.exp (-(s : ℂ) * ‖p.1.2‖^2) *
            Complex.exp (-Complex.I * spatialDot p.1.2 (spatialPart p.1.1 - spatialPart p.2))) := by
        have hx0 : Continuous (fun p : (SpaceTime × SpatialCoords) × SpaceTime => p.1.1 0) :=
          (PiLp.continuous_apply 2 (fun _ : Fin STDimension => ℝ) 0).comp
            (continuous_fst.comp continuous_fst)
        have hy0 : Continuous (fun p : (SpaceTime × SpatialCoords) × SpaceTime => p.2 0) :=
          (PiLp.continuous_apply 2 (fun _ : Fin STDimension => ℝ) 0).comp continuous_snd
        apply Continuous.mul
        · apply Continuous.mul
          · apply Continuous.mul
            · apply Continuous.mul
              · apply Continuous.mul
                · exact continuous_star.comp (hf_cont.comp (continuous_fst.comp continuous_fst))
                · exact hf_cont.comp continuous_snd
              · exact continuous_const
            · apply Complex.continuous_exp.comp
              apply Continuous.neg
              apply continuous_ofReal.comp
              apply Continuous.div_const
              apply Continuous.pow
              exact hx0.neg.sub hy0
          · apply Complex.continuous_exp.comp
            apply Continuous.mul continuous_const
            apply Continuous.pow
            exact continuous_ofReal.comp (continuous_norm.comp (continuous_snd.comp continuous_fst))
        · apply Complex.continuous_exp.comp
          apply Continuous.mul continuous_const
          apply continuous_ofReal.comp
          unfold spatialDot
          apply continuous_finsetSum
          intro i _
          have hk_i : Continuous (fun p : (SpaceTime × SpatialCoords) × SpaceTime => p.1.2 i) :=
            (PiLp.continuous_apply 2 (fun _ : Fin (STDimension - 1) => ℝ) i).comp
              (continuous_snd.comp continuous_fst)
          have hv_i : Continuous (fun p : (SpaceTime × SpatialCoords) × SpaceTime =>
              (spatialPart p.1.1 - spatialPart p.2) i) :=
            (PiLp.continuous_apply 2 (fun _ : Fin (STDimension - 1) => ℝ) i).comp
              ((continuous_spatialPart.comp (continuous_fst.comp continuous_fst)).sub
                (continuous_spatialPart.comp continuous_snd))
          exact hk_i.mul hv_i
      exact h_cont.aestronglyMeasurable
    · -- Norm bound: ‖F p‖ ≤ √(π/s) * ‖f(p.1.1)‖ * ‖f(p.2)‖ * exp(-s‖p.1.2‖²)
      filter_upwards with ⟨⟨x, k_sp⟩, y⟩
      simp only [F]
      exact (cexp6_norm_le_ksp f s hs.le x y k_sp).trans_eq (by ring)
  -- Apply Integrable.integral_prod_left to get integrability on (x, k)
  have h_outer : MeasureTheory.Integrable
      (fun p : SpaceTime × SpatialCoords => ∫ y : SpaceTime,
        (starRingEnd ℂ (f p.1)) * f y *
          (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(p.1 0) - y 0)^2 / (4 * s) : ℝ)) *
          Complex.exp (-(s : ℂ) * ‖p.2‖^2) *
          Complex.exp (-Complex.I * spatialDot p.2 (spatialPart p.1 - spatialPart y)))
      (MeasureTheory.volume.prod MeasureTheory.volume) :=
    h_F_integrable.integral_prod_left
  exact MeasureTheory.integral_integral_swap h_outer
