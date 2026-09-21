/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Examples.HeatSemigroup
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Gaussian averages and half the Laplacian on the line

Half the second derivative — half the Laplacian in one dimension — is the infinitesimal
generator of the Gaussian averages of a twice continuously differentiable function whose value
and second derivative vanish at infinity.  Writing `gaussianReal x t` for the normal law on the
line with mean `x` and variance `t`, and `x ↦ ∫ f d gaussianReal x t` for the Gaussian average
of `f` at scale `t` (at `t = 0` it is `f` itself), the difference quotient
`t⁻¹ (∫ f d gaussianReal x t - f x)` converges to `f'' x / 2` as `t → 0⁺`, uniformly in the
centre `x`.  The argument is the classical one: rescaling by `√t` reduces every average to the
standard normal law, and a second-order Taylor expansion at `x` splits the increment into a term
of first order whose Gaussian mean vanishes, a term of second order whose Gaussian mean is
`t f'' x / 2`, and a remainder bounded by the modulus of continuity of `f''` on the bulk of the
law and by its fourth moment on the tail.  Neither bound depends on `x`, whence the uniformity.

Main results:

* `abs_sub_taylor_two_le`, the second-order Taylor estimate with a modulus: the second-order
  Taylor polynomial of `f` at `x` approximates `f (x + h)` to within `C h²` as soon as the
  increment of `f''` over the segment from `x` to `x + h` is at most `C`;
* `tendstoUniformly_gaussianAverage_sub_div`, the limit above, as a `TendstoUniformly`
  statement;
* `gaussianAverage`, the Gaussian average of a continuous function vanishing at infinity: the
  `C₀` action of the heat semigroup of `Examples/HeatSemigroup.lean`, and
  `tendsto_gaussianAverage_sub_div`, the same limit read as convergence in the `C₀` norm;
* `c0Semigroup_heatSemigroup_apply`, `tendsto_differenceQuotient_heatSemigroup`,
  `mem_generatorDomain_heatSemigroup` and `generator_heatSemigroup`: twice continuously
  differentiable `C₀` functions with `C₀` second derivative lie in the generator domain of the
  `C₀` semigroup of the heat semigroup, and the generator is half the second derivative there,
  in the sense of `Semigroup/Generator.lean`.

No partial differential equation is solved, the generator domain is not characterized (only
contained), and nothing is claimed in dimension greater than one or for a function outside the
stated smoothness class.
-/

noncomputable section PortComputability

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ZeroAtInfty

namespace MarkovProcess

section

section Taylor

variable {f : ℝ → ℝ}

/-- **Second-order Taylor estimate with a modulus.**  If the increment of the second derivative
of `f` is at most `C` on the segment from `x` to `x + h`, then the second-order Taylor
polynomial of `f` at `x` approximates `f (x + h)` to within `C h²`. -/
theorem abs_sub_taylor_two_le (hf : ContDiff ℝ 2 f) (x h C : ℝ)
    (hC : ∀ s ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv 2 f (x + s * h) - iteratedDeriv 2 f x| ≤ C) :
    |f (x + h) - f x - h * deriv f x - h ^ 2 / 2 * iteratedDeriv 2 f x| ≤ C * h ^ 2 := by
  have hd2 : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hdf : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hddf : Differentiable ℝ (deriv f) := hd2.differentiable (by norm_num)
  have hiter : ∀ y : ℝ, deriv (deriv f) y = iteratedDeriv 2 f y := by
    intro y; rw [iteratedDeriv_succ, iteratedDeriv_one]
  set c := iteratedDeriv 2 f x with hcdef
  have hinner : ∀ s : ℝ, HasDerivAt (fun s : ℝ ↦ x + s * h) h s := by
    intro s
    simpa using (((hasDerivAt_id s).mul_const h).const_add x)
  set F : ℝ → ℝ :=
    fun s ↦ f (x + s * h) - f x - s * (h * deriv f x) - s ^ 2 * (h ^ 2 * c / 2) with hFdef
  set G : ℝ → ℝ := fun s ↦ h * deriv f (x + s * h) - h * deriv f x - s * (h ^ 2 * c) with hGdef
  have hFderiv : ∀ s : ℝ, HasDerivAt F (G s) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ ↦ f (x + s * h)) (deriv f (x + s * h) * h) s :=
      (hdf (x + s * h)).hasDerivAt.comp s (hinner s)
    have h2 : HasDerivAt (fun s : ℝ ↦ s * (h * deriv f x)) (h * deriv f x) s := by
      simpa using (hasDerivAt_id s).mul_const (h * deriv f x)
    have h3 : HasDerivAt (fun s : ℝ ↦ s ^ 2 * (h ^ 2 * c / 2)) (2 * s * (h ^ 2 * c / 2)) s := by
      have hp : HasDerivAt (fun s : ℝ ↦ s ^ 2) (2 * s) s := by simpa using hasDerivAt_pow 2 s
      exact hp.mul_const _
    have hsum := ((h1.sub_const (f x)).sub h2).sub h3
    convert hsum using 1
    all_goals first | rfl | ring
  have hGderiv : ∀ s : ℝ, HasDerivAt G (h ^ 2 * (iteratedDeriv 2 f (x + s * h) - c)) s := by
    intro s
    have h1 := (hddf (x + s * h)).hasDerivAt.comp s (hinner s)
    simp only [Function.comp_def, hiter] at h1
    have h2 : HasDerivAt (fun s : ℝ ↦ s * (h ^ 2 * c)) (h ^ 2 * c) s := by
      simpa using (hasDerivAt_id s).mul_const (h ^ 2 * c)
    have hsum := ((h1.const_mul h).sub_const (h * deriv f x)).sub h2
    convert hsum using 1
    all_goals first | rfl | ring
  have hCnn : 0 ≤ C := by
    have h0 := hC 0 (by norm_num)
    rw [zero_mul, add_zero, ← hcdef, sub_self, abs_zero] at h0
    exact h0
  have hconv : Convex ℝ (Set.Icc (0 : ℝ) 1) := convex_Icc 0 1
  have hG0 : G 0 = 0 := by simp [hGdef]
  have hF0 : F 0 = 0 := by simp [hFdef]
  have hGbound : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖G s‖ ≤ C * h ^ 2 := by
    intro s hs
    have hkey : ‖G s - G 0‖ ≤ C * h ^ 2 * ‖s - 0‖ := by
      refine hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun u _ ↦ (hGderiv u).hasDerivWithinAt) (fun u hu ↦ ?_) (by norm_num) hs
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg h)]
      calc h ^ 2 * |iteratedDeriv 2 f (x + u * h) - c| ≤ h ^ 2 * C :=
            mul_le_mul_of_nonneg_left (hC u hu) (sq_nonneg h)
        _ = C * h ^ 2 := by ring
    rw [hG0, sub_zero] at hkey
    refine hkey.trans ?_
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hs.1]
    nlinarith [mul_nonneg hCnn (sq_nonneg h), hs.1, hs.2]
  have hFbound : ‖F 1 - F 0‖ ≤ C * h ^ 2 * ‖(1 : ℝ) - 0‖ :=
    hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u _ ↦ (hFderiv u).hasDerivWithinAt) hGbound (by norm_num) (by norm_num)
  rw [hF0, sub_zero, Real.norm_eq_abs] at hFbound
  simp only [hFdef, one_mul, one_pow] at hFbound
  calc |f (x + h) - f x - h * deriv f x - h ^ 2 / 2 * c|
      = |f (x + h) - f x - 1 * (h * deriv f x) - 1 * (h ^ 2 * c / 2)| := by ring_nf
    _ ≤ C * h ^ 2 * ‖(1 : ℝ) - 0‖ := by simpa using hFbound
    _ = C * h ^ 2 := by norm_num

end Taylor

section Gaussian

/-- All polynomial moments of the standard normal law are finite. -/
private theorem integrable_pow_gaussian (n : ℕ) :
    Integrable (fun z : ℝ ↦ z ^ n) (gaussianReal 0 1) :=
  integrable_pow_of_mem_interior_integrableExpSet (by simp) n

/-- The first moment of the standard normal law vanishes. -/
private theorem integral_id_gaussian : ∫ z : ℝ, z ∂(gaussianReal 0 1) = 0 :=
  integral_id_gaussianReal

/-- The second moment of the standard normal law is one. -/
private theorem integral_sq_gaussian : ∫ z : ℝ, z ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have hvar : Var[fun z : ℝ ↦ z; gaussianReal 0 1] = ((1 : ℝ≥0) : ℝ) :=
    variance_fun_id_gaussianReal
  rw [variance_eq_integral (by fun_prop), integral_id_gaussianReal] at hvar
  simpa using hvar

/-- The fourth moment of the standard normal law. -/
private def gaussianMoment4 : ℝ := ∫ z : ℝ, z ^ 4 ∂(gaussianReal 0 1)

private theorem gaussianMoment4_nonneg : 0 ≤ gaussianMoment4 :=
  integral_nonneg fun z ↦ by positivity

/-- The Gaussian average, read on the standard normal law. -/
private theorem integral_gaussian_eq (g : ℝ → ℝ) (hg : Continuous g) (x : ℝ) (t : ℝ≥0) :
    ∫ y, g y ∂gaussianReal x t = ∫ z, g (x + Real.sqrt t * z) ∂(gaussianReal 0 1) := by
  rw [gaussianReal_eq_map_add_sqrt_mul x t, integral_map (by fun_prop) hg.aestronglyMeasurable]

end Gaussian

section Estimate

variable {f : ℝ → ℝ}

/-- A pure-algebra step: away from the origin a constant is dominated by a quadratic. -/
private theorem le_mul_sq_div {M a b : ℝ} (hM : 0 ≤ M) (hb : 0 < b) (hab : b ≤ |a|) :
    M ≤ M * a ^ 2 / b ^ 2 := by
  have hsq : b ^ 2 ≤ a ^ 2 := by nlinarith [sq_abs a, abs_nonneg a]
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- **The quantitative estimate.**  If the second derivative of `f` is bounded by `M` and varies
by at most `ε` over distances smaller than `δ`, then the Gaussian difference quotient at scale
`t` differs from half the second derivative by at most `ε` plus a term of order `t`, uniformly
in the centre `x`. -/
private theorem abs_gaussianQuotient_sub_le (hf : ContDiff ℝ 2 f) {B M ε δ : ℝ}
    (hB : ∀ y, |f y| ≤ B) (hM : ∀ y, |iteratedDeriv 2 f y| ≤ M) (hε : 0 ≤ ε) (hδ : 0 < δ)
    (hunif : ∀ u v : ℝ, |u - v| < δ → |iteratedDeriv 2 f u - iteratedDeriv 2 f v| ≤ ε)
    {t : ℝ≥0} (ht : 0 < (t : ℝ)) (x : ℝ) :
    |(t : ℝ)⁻¹ * (∫ y, f y ∂gaussianReal x t - f x) - iteratedDeriv 2 f x / 2| ≤
      ε + 2 * M * (t : ℝ) * gaussianMoment4 / δ ^ 2 := by
  have hMnn : 0 ≤ M := le_trans (abs_nonneg _) (hM x)
  set σ := Real.sqrt (t : ℝ) with hσdef
  have hσ2 : σ ^ 2 = (t : ℝ) := Real.sq_sqrt t.coe_nonneg
  set c := iteratedDeriv 2 f x with hcdef
  have hcont : Continuous f := hf.continuous
  have hz1 : Integrable (fun z : ℝ ↦ z) (gaussianReal 0 1) := by
    simpa using integrable_pow_gaussian 1
  have hz2 : Integrable (fun z : ℝ ↦ z ^ 2) (gaussianReal 0 1) := integrable_pow_gaussian 2
  have hz4 : Integrable (fun z : ℝ ↦ z ^ 4) (gaussianReal 0 1) := integrable_pow_gaussian 4
  have hshift : Integrable (fun z : ℝ ↦ f (x + σ * z)) (gaussianReal 0 1) := by
    refine Integrable.mono' (integrable_const B)
      ((hcont.comp (by fun_prop)).aestronglyMeasurable) ?_
    filter_upwards with z
    simpa using hB (x + σ * z)
  have hchange : ∫ y, f y ∂gaussianReal x t = ∫ z, f (x + σ * z) ∂(gaussianReal 0 1) :=
    integral_gaussian_eq f hcont x t
  set E : ℝ → ℝ :=
    fun z ↦ f (x + σ * z) - f x - σ * z * deriv f x - (σ * z) ^ 2 / 2 * c with hEdef
  have h1 : Integrable (fun z : ℝ ↦ σ * z * deriv f x) (gaussianReal 0 1) := by
    have h := hz1.const_mul (σ * deriv f x)
    have heq : (fun z : ℝ ↦ σ * deriv f x * z) = fun z : ℝ ↦ σ * z * deriv f x := by
      funext z; ring
    rwa [heq] at h
  have h2 : Integrable (fun z : ℝ ↦ (σ * z) ^ 2 / 2 * c) (gaussianReal 0 1) := by
    have h := hz2.const_mul (σ ^ 2 * c / 2)
    have heq : (fun z : ℝ ↦ σ ^ 2 * c / 2 * z ^ 2) = fun z : ℝ ↦ (σ * z) ^ 2 / 2 * c := by
      funext z; ring
    rwa [heq] at h
  have hEint : Integrable E (gaussianReal 0 1) :=
    ((hshift.sub (integrable_const (f x))).sub h1).sub h2
  have hI1 : ∫ z : ℝ, σ * z * deriv f x ∂(gaussianReal 0 1) = 0 := by
    have heq : (fun z : ℝ ↦ σ * z * deriv f x) = fun z : ℝ ↦ σ * deriv f x * z := by
      funext z; ring
    rw [heq, integral_const_mul, integral_id_gaussian, mul_zero]
  have hI2 : ∫ z : ℝ, (σ * z) ^ 2 / 2 * c ∂(gaussianReal 0 1) = (t : ℝ) * c / 2 := by
    have heq : (fun z : ℝ ↦ (σ * z) ^ 2 / 2 * c) = fun z : ℝ ↦ σ ^ 2 * c / 2 * z ^ 2 := by
      funext z; ring
    rw [heq, integral_const_mul, integral_sq_gaussian, mul_one, hσ2]
  have hE : ∫ z, E z ∂(gaussianReal 0 1)
      = (∫ z, f (x + σ * z) ∂(gaussianReal 0 1)) - f x - (t : ℝ) * c / 2 := by
    have e1 : ∫ z, E z ∂(gaussianReal 0 1)
        = (∫ z, (f (x + σ * z) - f x - σ * z * deriv f x) ∂(gaussianReal 0 1))
          - ∫ z, ((σ * z) ^ 2 / 2 * c) ∂(gaussianReal 0 1) :=
      integral_sub ((hshift.sub (integrable_const (f x))).sub h1) h2
    have e2 : ∫ z, (f (x + σ * z) - f x - σ * z * deriv f x) ∂(gaussianReal 0 1)
        = (∫ z, (f (x + σ * z) - f x) ∂(gaussianReal 0 1))
          - ∫ z, (σ * z * deriv f x) ∂(gaussianReal 0 1) :=
      integral_sub (hshift.sub (integrable_const (f x))) h1
    have e3 : ∫ z, (f (x + σ * z) - f x) ∂(gaussianReal 0 1)
        = (∫ z, f (x + σ * z) ∂(gaussianReal 0 1)) - ∫ _z : ℝ, f x ∂(gaussianReal 0 1) :=
      integral_sub hshift (integrable_const (f x))
    have e4 : ∫ _z : ℝ, f x ∂(gaussianReal 0 1) = f x := by simp
    rw [e1, e2, e3, e4, hI1, hI2]
    ring
  have hEbound : ∀ z : ℝ,
      |E z| ≤ ε * (t : ℝ) * z ^ 2 + 2 * M * (t : ℝ) ^ 2 / δ ^ 2 * z ^ 4 := by
    intro z
    have hCbound : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        |iteratedDeriv 2 f (x + s * (σ * z)) - iteratedDeriv 2 f x| ≤
          ε + 2 * M * (σ * z) ^ 2 / δ ^ 2 := by
      intro s hs
      rcases lt_or_ge |σ * z| δ with hlt | hge
      · have hclose : |x + s * (σ * z) - x| < δ := by
          rw [add_sub_cancel_left, abs_mul, abs_of_nonneg hs.1]
          calc s * |σ * z| ≤ 1 * |σ * z| :=
                mul_le_mul_of_nonneg_right hs.2 (abs_nonneg _)
            _ = |σ * z| := one_mul _
            _ < δ := hlt
        have hpos : 0 ≤ 2 * M * (σ * z) ^ 2 / δ ^ 2 := by positivity
        linarith [hunif _ _ hclose]
      · have habs : |iteratedDeriv 2 f (x + s * (σ * z)) - iteratedDeriv 2 f x| ≤ 2 * M := by
          calc |iteratedDeriv 2 f (x + s * (σ * z)) - iteratedDeriv 2 f x|
              ≤ |iteratedDeriv 2 f (x + s * (σ * z))| + |iteratedDeriv 2 f x| := abs_sub _ _
            _ ≤ M + M := add_le_add (hM _) (hM _)
            _ = 2 * M := by ring
        have hstep : 2 * M ≤ 2 * M * (σ * z) ^ 2 / δ ^ 2 :=
          le_mul_sq_div (by linarith) hδ hge
        linarith
    have htaylor := abs_sub_taylor_two_le hf x (σ * z) _ hCbound
    refine le_trans htaylor (le_of_eq ?_)
    have hsq : (σ * z) ^ 2 = (t : ℝ) * z ^ 2 := by rw [mul_pow, hσ2]
    rw [hsq]
    field_simp
  have hboundInt : Integrable
      (fun z : ℝ ↦ ε * (t : ℝ) * z ^ 2 + 2 * M * (t : ℝ) ^ 2 / δ ^ 2 * z ^ 4)
      (gaussianReal 0 1) := (hz2.const_mul _).add (hz4.const_mul _)
  have hIabs : |∫ z, E z ∂(gaussianReal 0 1)| ≤
      ε * (t : ℝ) + 2 * M * (t : ℝ) ^ 2 / δ ^ 2 * gaussianMoment4 := by
    calc |∫ z, E z ∂(gaussianReal 0 1)| ≤ ∫ z, |E z| ∂(gaussianReal 0 1) :=
          abs_integral_le_integral_abs
      _ ≤ ∫ z, (ε * (t : ℝ) * z ^ 2 + 2 * M * (t : ℝ) ^ 2 / δ ^ 2 * z ^ 4) ∂(gaussianReal 0 1) :=
          integral_mono hEint.abs hboundInt hEbound
      _ = ε * (t : ℝ) + 2 * M * (t : ℝ) ^ 2 / δ ^ 2 * gaussianMoment4 := by
          rw [integral_add (hz2.const_mul _) (hz4.const_mul _), integral_const_mul,
            integral_const_mul, integral_sq_gaussian, mul_one, gaussianMoment4]
  have hkey : (t : ℝ)⁻¹ * (∫ y, f y ∂gaussianReal x t - f x) - c / 2
      = (t : ℝ)⁻¹ * ∫ z, E z ∂(gaussianReal 0 1) := by
    rw [hchange, hE]
    field_simp
  rw [hkey, abs_mul, abs_of_nonneg (inv_nonneg.mpr ht.le)]
  calc (t : ℝ)⁻¹ * |∫ z, E z ∂(gaussianReal 0 1)|
      ≤ (t : ℝ)⁻¹ * (ε * (t : ℝ) + 2 * M * (t : ℝ) ^ 2 / δ ^ 2 * gaussianMoment4) :=
        mul_le_mul_of_nonneg_left hIabs (inv_nonneg.mpr ht.le)
    _ = ε + 2 * M * (t : ℝ) * gaussianMoment4 / δ ^ 2 := by
        field_simp

end Estimate

section Uniform

variable {f : ℝ → ℝ}

/-- A continuous function vanishing at infinity is bounded and uniformly continuous. -/
private theorem exists_bound_modulus {g : ℝ → ℝ} (hg : Continuous g)
    (hg0 : Tendsto g (cocompact ℝ) (𝓝 0)) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ y, |g y| ≤ M) ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ u v : ℝ, |u - v| < δ → |g u - g v| ≤ ε := by
  set G : C₀(ℝ, ℝ) := ⟨⟨g, hg⟩, hg0⟩ with hG
  refine ⟨‖G‖, norm_nonneg _, fun y ↦ ?_, fun ε hε ↦ ?_⟩
  · exact norm_apply_le_norm_c0 G y
  · obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuous_iff.mp
      (ZeroAtInftyContinuousMap.uniformContinuous G) ε hε
    refine ⟨δ, hδ, fun u v huv ↦ le_of_lt ?_⟩
    have hd := h (a := u) (b := v) (by rwa [Real.dist_eq])
    rwa [Real.dist_eq] at hd

/-- **Half the Laplacian generates the Gaussian averages.**  For a twice continuously
differentiable `f` whose value and second derivative vanish at infinity, the difference quotient
of the Gaussian average of `f` at scale `t`, taken at the centre `x`, converges as `t → 0⁺` to
half the second derivative of `f` at `x`, uniformly in `x`. -/
theorem tendstoUniformly_gaussianAverage_sub_div (hf : ContDiff ℝ 2 f)
    (hf0 : Tendsto f (cocompact ℝ) (𝓝 0))
    (hf2 : Tendsto (iteratedDeriv 2 f) (cocompact ℝ) (𝓝 0)) :
    TendstoUniformly (fun (t : ℝ≥0) (x : ℝ) ↦ (t : ℝ)⁻¹ * (∫ y, f y ∂gaussianReal x t - f x))
      (fun x ↦ iteratedDeriv 2 f x / 2) (𝓝[>] 0) := by
  obtain ⟨B, -, hB, -⟩ := exists_bound_modulus hf.continuous hf0
  obtain ⟨M, hMnn, hM, hmod⟩ :=
    exists_bound_modulus (hf.continuous_iteratedDeriv 2 (by norm_num)) hf2
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := hmod (ε / 2) (by linarith)
  have hKnn : 0 ≤ 2 * M * gaussianMoment4 :=
    mul_nonneg (by linarith) gaussianMoment4_nonneg
  have hK : 0 < 2 * M * gaussianMoment4 + 1 := by linarith
  set T : ℝ := ε * δ ^ 2 / (2 * (2 * M * gaussianMoment4 + 1)) with hT
  have hTpos : 0 < T := div_pos (mul_pos hε (pow_pos hδ 2)) (by linarith)
  have hev : ∀ᶠ t : ℝ≥0 in 𝓝[>] 0, (t : ℝ) < T := by
    have hopen : IsOpen {t : ℝ≥0 | (t : ℝ) < T} :=
      isOpen_lt NNReal.continuous_coe continuous_const
    have hmem : (0 : ℝ≥0) ∈ {t : ℝ≥0 | (t : ℝ) < T} := by simpa using hTpos
    exact mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds hmem)
  filter_upwards [hev, self_mem_nhdsWithin] with t htT htpos
  intro x
  have htpos' : (0 : ℝ) < (t : ℝ) := NNReal.coe_pos.mpr htpos
  have hmain := abs_gaussianQuotient_sub_le hf hB hM (by linarith : (0 : ℝ) ≤ ε / 2) hδ hδ'
    htpos' x
  rw [Real.dist_eq, abs_sub_comm]
  refine lt_of_le_of_lt hmain ?_
  have hKt : (2 * M * gaussianMoment4 + 1) * (t : ℝ)
      < (2 * M * gaussianMoment4 + 1) * T := mul_lt_mul_of_pos_left htT hK
  have hTval : (2 * M * gaussianMoment4 + 1) * T = ε * δ ^ 2 / 2 := by
    rw [hT]; field_simp
  have hprod : 2 * M * gaussianMoment4 * (t : ℝ) < ε * δ ^ 2 / 2 := by
    nlinarith [hKt, hTval, htpos'.le]
  have hbound : 2 * M * (t : ℝ) * gaussianMoment4 / δ ^ 2 < ε / 2 := by
    rw [div_lt_iff₀ (pow_pos hδ 2)]
    nlinarith [hprod]
  linarith

end Uniform

section C0

/-- **The Gaussian average of a `C₀` function.**  At scale `t` it is the integral of `f` against
the normal law centred at `x` with variance `t`; at `t = 0` it is `f` itself. -/
def gaussianAverage (f : C₀(ℝ, ℝ)) (t : ℝ≥0) : C₀(ℝ, ℝ) :=
  heatSemigroup.c0KernelIntegral mapsC0_heatSemigroup t f

@[simp]
theorem gaussianAverage_apply (f : C₀(ℝ, ℝ)) (t : ℝ≥0) (x : ℝ) :
    gaussianAverage f t x = ∫ y, f y ∂gaussianReal x t := by
  rw [gaussianAverage, SubMarkovKernelSemigroup.c0KernelIntegral_apply, kernelIntegral,
    heatSemigroup_apply]

/-- **Half the Laplacian generates the Gaussian averages, in the `C₀` norm.**  If `f` is a `C₀`
function which is twice continuously differentiable and whose second derivative is the `C₀`
function `g`, then the difference quotients of the Gaussian averages of `f` converge in the
`C₀` norm to `g / 2` as the scale tends to zero. -/
theorem tendsto_gaussianAverage_sub_div (f g : C₀(ℝ, ℝ)) (hf : ContDiff ℝ 2 (f : ℝ → ℝ))
    (hg : ∀ x, g x = iteratedDeriv 2 (f : ℝ → ℝ) x) :
    Tendsto (fun t : ℝ≥0 ↦ (t : ℝ)⁻¹ • (gaussianAverage f t - f)) (𝓝[>] 0)
      (𝓝 ((2 : ℝ)⁻¹ • g)) := by
  have hgf : iteratedDeriv 2 (f : ℝ → ℝ) = (g : ℝ → ℝ) := funext fun x ↦ (hg x).symm
  have hf2 : Tendsto (iteratedDeriv 2 (f : ℝ → ℝ)) (cocompact ℝ) (𝓝 0) := by
    rw [hgf]; exact g.zero_at_infty'
  have huniform := tendstoUniformly_gaussianAverage_sub_div hf f.zero_at_infty' hf2
  rw [ZeroAtInftyContinuousMap.tendsto_iff_tendstoUniformly]
  have hlim : (fun x : ℝ ↦ iteratedDeriv 2 (f : ℝ → ℝ) x / 2) = ⇑((2 : ℝ)⁻¹ • g) := by
    funext x
    rw [hgf]
    simp [div_eq_inv_mul]
  have hfun : (fun t : ℝ≥0 ↦ ⇑((t : ℝ)⁻¹ • (gaussianAverage f t - f)))
      = fun (t : ℝ≥0) (x : ℝ) ↦ (t : ℝ)⁻¹ * (∫ y, f y ∂gaussianReal x t - f x) := by
    funext t x
    simp
  rw [← hlim, hfun]
  exact huniform

/-- The `C₀` semigroup of the heat semigroup acts by Gaussian averages. -/
theorem c0Semigroup_heatSemigroup_apply (f : C₀(ℝ, ℝ)) (t : ℝ≥0) :
    isFellerKernelSemigroup_heatSemigroup.c0Semigroup t f = gaussianAverage f t :=
  ZeroAtInftyContinuousMap.ext fun x ↦ by
    rw [SubMarkovKernelSemigroup.IsFellerKernelSemigroup.c0Semigroup_apply_apply,
      gaussianAverage_apply, kernelIntegral, heatSemigroup_apply]

/-- The difference quotients of the heat semigroup converge, in the `C₀` norm, to half the
second derivative. -/
theorem tendsto_differenceQuotient_heatSemigroup (f g : C₀(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) (hg : ∀ x, g x = iteratedDeriv 2 (f : ℝ → ℝ) x) :
    Tendsto (fun t : ℝ≥0 ↦
        (t : ℝ)⁻¹ • (isFellerKernelSemigroup_heatSemigroup.c0Semigroup t f - f))
      (𝓝[>] 0) (𝓝 ((2 : ℝ)⁻¹ • g)) := by
  simpa only [c0Semigroup_heatSemigroup_apply] using tendsto_gaussianAverage_sub_div f g hf hg

/-- **Twice continuously differentiable `C₀` functions with `C₀` second derivative lie in the
generator domain of the heat semigroup.** -/
theorem mem_generatorDomain_heatSemigroup (f g : C₀(ℝ, ℝ)) (hf : ContDiff ℝ 2 (f : ℝ → ℝ))
    (hg : ∀ x, g x = iteratedDeriv 2 (f : ℝ → ℝ) x) :
    f ∈ isFellerKernelSemigroup_heatSemigroup.c0Semigroup.generatorDomain :=
  isFellerKernelSemigroup_heatSemigroup.c0Semigroup.mem_generatorDomain_of_tendsto
    (tendsto_differenceQuotient_heatSemigroup f g hf hg)

/-- **The generator of the heat semigroup is half the Laplacian**: on a twice continuously
differentiable `C₀` function `f` with `C₀` second derivative `g`, the generator of the `C₀`
semigroup of Brownian motion is `g / 2`. -/
theorem generator_heatSemigroup (f g : C₀(ℝ, ℝ)) (hf : ContDiff ℝ 2 (f : ℝ → ℝ))
    (hg : ∀ x, g x = iteratedDeriv 2 (f : ℝ → ℝ) x) :
    isFellerKernelSemigroup_heatSemigroup.c0Semigroup.generator
      ⟨f, mem_generatorDomain_heatSemigroup f g hf hg⟩ = (2 : ℝ)⁻¹ • g :=
  isFellerKernelSemigroup_heatSemigroup.c0Semigroup.generator_mk_eq
    (tendsto_differenceQuotient_heatSemigroup f g hf hg)

end C0

end

end MarkovProcess

end PortComputability
