/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/


import LeanPool.OSforGFF.Spacetime.Basic
import LeanPool.OSforGFF.OS.Axioms
import LeanPool.OSforGFF.Measure.Construct
import LeanPool.OSforGFF.Spacetime.ComplexTestFunction

/-!
# OS0 — Analyticity of the Generating Functional

Proves that Z[∑ᵢ zᵢ fᵢ] = ∫ exp(i ∑ᵢ zᵢ ⟨φ, fᵢ⟩) dμ(φ) is analytic in the complex
parameters zᵢ.

## Strategy

For a centered Gaussian measure with covariance C, the complex generating
functional has the closed form:
  Z[f] = exp(-½ C_ℂ(f, f))
where C_ℂ is the complexified covariance bilinear form (freeCovarianceℂBilinear).

Since C_ℂ is ℂ-bilinear:
  Z[∑ᵢ zᵢ Jᵢ] = exp(-½ ∑ᵢⱼ zᵢ zⱼ C_ℂ(Jᵢ, Jⱼ))
This is exp(quadratic polynomial in z), which is analytic on ℂⁿ.

## Proof strategy for `gff_complex_CF_covariance`

1-parameter analytic continuation: decompose f = f_re + I·f_im, define
L(t) = Z[f_re + t·f_im] and R(t) = exp(-½ Q(t)), show L = R on ℝ (from
`gff_real_characteristic`), extend to ℂ via the identity theorem, evaluate at t = I.

## Key Lemma

- `gff_cf_slice_entire`: t ↦ Z[f_re + t·f_im] is entire.
  Proved via Fernique integrability + parameter-dependent holomorphy of integrals.

## Main result

- `gaussianFreeField_satisfies_OS0`
-/

noncomputable section

open MeasureTheory Complex BigOperators SchwartzMap
open scoped MeasureTheory ComplexConjugate

namespace QFT

/-! ## OS0 for the Gaussian Free Field -/

/-! ### Preconditions for GFF Generating Functional Analyticity

These lemmas establish the preconditions needed for the analyticity proof.
The generating functional is:

  Z[J] = ∫ exp(i⟨ω, J⟩) dμ(ω)

where dμ is the Gaussian measure on field configurations.
-/

/-- Young's inequality `c·|x| ≤ c²/(4α) + α·x²` for `α > 0`, used to dominate
    linear-exponent integrands by Gaussian-square (Fernique) integrands. -/
private lemma young_ineq (c α : ℝ) (hα : 0 < α) (x : ℝ) :
    c * |x| ≤ c ^ 2 / (4 * α) + α * x ^ 2 := by
  rw [show c ^ 2 / (4 * α) + α * x ^ 2 = (c ^ 2 + 4 * α ^ 2 * x ^ 2) / (4 * α) from by field_simp,
    le_div_iff₀ (by positivity : (0:ℝ) < 4 * α)]
  nlinarith [sq_nonneg (c - 2 * α * |x|), sq_abs x]

variable (m : ℝ) [Fact (0 < m)]

/-- The complex pairing is continuous in ω.
    This follows from the continuity of the evaluation map on WeakDual.
-/
theorem distributionPairingℂ_real_continuous (f : TestFunctionℂ) :
    Continuous (fun ω : FieldConfiguration => distributionPairingℂReal ω f) := by
  -- distributionPairingℂReal ω f = ω f_re + I * ω f_im; each evaluation is continuous.
  simp only [distributionPairingℂReal, complexTestFunctionDecompose]
  exact (Complex.continuous_ofReal.comp (WeakDual.eval_continuous _)).add
    (continuous_const.mul (Complex.continuous_ofReal.comp (WeakDual.eval_continuous _)))

/-- The complex pairing is measurable in ω (cylinder σ-algebra version).
    This follows from the measurability of the evaluation map on WeakDual.
-/
lemma distributionPairingℂ_real_measurable (f : TestFunctionℂ) :
    Measurable (fun ω : FieldConfiguration => distributionPairingℂReal ω f) := by
  simp only [distributionPairingℂReal, complexTestFunctionDecompose]
  exact (continuous_ofReal.measurable.comp (WeakDual.eval_measurable _)).add
    (measurable_const.mul (continuous_ofReal.measurable.comp (WeakDual.eval_measurable _)))

/-- The GFF integrand for the generating functional is measurable in ω for each z. -/
theorem gff_integrand_measurable
    (n : ℕ) (J : Fin n → TestFunctionℂ) (z : Fin n → ℂ) :
    AEStronglyMeasurable
      (fun ω : FieldConfiguration =>
        Complex.exp (Complex.I * distributionPairingℂReal ω (∑ i, z i • J i)))
      (muGFF m).toMeasure := by
  exact (Complex.continuous_exp.measurable.comp
    (measurable_const.mul (distributionPairingℂ_real_measurable _))).aestronglyMeasurable

/-- The GFF integrand is analytic in z for each fixed field configuration ω.
    This follows from the fact that:
    1. z ↦ ∑ᵢ zᵢ • Jᵢ is linear (hence analytic) in z
    2. ω ↦ ⟨ω, f⟩ is linear in f
    3. exp(i · _) is entire
-/
theorem gff_integrand_analytic
    (n : ℕ) (J : Fin n → TestFunctionℂ) (ω : FieldConfiguration) (z₀ : Fin n → ℂ) :
    AnalyticAt ℂ
      (fun z : Fin n → ℂ =>
        Complex.exp (Complex.I * distributionPairingℂReal ω (∑ i, z i • J i)))
      z₀ := by
  -- exp is entire; the argument is linear (hence analytic) in z.
  apply AnalyticAt.cexp
  apply analyticAt_const.mul
  -- z ↦ distributionPairingℂReal ω (∑ i, z i • J i) = ∑ i, z i * pairing(J i), a polynomial.
  have h_linear : ∀ z : Fin n → ℂ, distributionPairingℂReal ω (∑ i, z i • J i) =
      ∑ i, z i * distributionPairingℂReal ω (J i) := fun z => by
    induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
    | empty => simpa using (pairing_linear_combo ω 0 0 0 0)
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
      simpa only [one_smul, one_mul] using
        pairing_linear_combo ω (J i) (∑ j ∈ s, z j • J j) (z i) 1
  simp_rw [h_linear]
  refine Finset.analyticAt_fun_sum _ fun i _ => ?_
  exact (ContinuousLinearMap.analyticAt (ContinuousLinearMap.proj (R := ℂ) i) z₀).mul
    analyticAt_const

/-- The norm of exp(I * distributionPairingℂReal ω f) equals exp(-(ω f_im))
    where f_im is the imaginary part of the complex test function.

    Proof: For a complex test function f with real/imaginary parts f_re, f_im:
    - distributionPairingℂReal ω f = (ω f_re) + I * (ω f_im)
    - I * distributionPairingℂReal ω f = I * (ω f_re) - (ω f_im)
    - Re(I * distributionPairingℂReal ω f) = -(ω f_im)
    - ‖exp(z)‖ = exp(Re(z)), so ‖exp(I * ...)‖ = exp(-(ω f_im))
-/
lemma norm_exp_I_distributionPairingℂ_real (f : TestFunctionℂ) (ω : FieldConfiguration) :
    ‖Complex.exp (Complex.I * distributionPairingℂReal ω f)‖ =
      Real.exp (-(ω (complexTestFunctionDecompose f).2)) := by
  -- Use Complex.norm_exp: ‖exp(z)‖ = exp(z.re)
  rw [Complex.norm_exp]
  -- Need to show: (I * distributionPairingℂReal ω f).re = -(ω f_im)
  congr 1
  -- Expand distributionPairingℂReal
  simp only [distributionPairingℂReal, complexTestFunctionDecompose]
  -- I * ((ω f_re : ℂ) + I * (ω f_im : ℂ)) = I * (ω f_re) - (ω f_im)
  -- The real part is -(ω f_im)
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.add_re, Complex.ofReal_re,
             Complex.add_im, Complex.ofReal_im, Complex.mul_im]
  ring

/-- Integrability of exp(-ω f) for a real test function f under the GFF measure.
    This follows from the Gaussian nature: for centered Gaussian X with variance σ²,
    E[exp(-X)] = exp(σ²/2).
-/
lemma gff_exp_neg_pairing_integrable (f : TestFunction) :
    Integrable (fun ω : FieldConfiguration => Real.exp (-(ω f)))
      (muGFF m).toMeasure := by
  -- Fernique: exp(α x²) is integrable, and exp(-x) ≤ exp(1/(4α)) · exp(α x²) (Young, c = 1).
  obtain ⟨α, hα_pos, h_integ⟩ := gaussianFreeField_pairing_expSq_integrable m f
  refine (h_integ.const_mul (Real.exp (1 / (4 * α)))).mono'
    ((Real.continuous_exp.measurable.comp (measurable_neg.comp (WeakDual.eval_measurable
       f))).aestronglyMeasurable) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), distributionPairingCLM_apply,
    distributionPairing, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have := young_ineq 1 α hα_pos (ω f)
  rw [one_mul] at this
  linarith [neg_abs_le (ω f), this]

/-- exp(|ω f|) is in L^2 (and in fact all L^p) under the GFF measure.
    This follows from Fernique's theorem: if exp(α x²) is integrable, then exp(|x|)^p is integrable
    for all p < ∞ because |x|^p ≤ C_p * exp(ε x²) for small ε.
-/
lemma gff_exp_abs_pairing_memLp (f : TestFunction) (p : ENNReal) (hp : p ≠ ⊤) :
    MemLp (fun ω : FieldConfiguration => Real.exp |ω f|) p (muGFF m).toMeasure := by
  -- By Fernique, ∃ α > 0 such that exp(α x²) is integrable
  obtain ⟨α, hα_pos, h_fernique⟩ := gaussianFreeField_pairing_expSq_integrable m f
  have h_aesm : AEStronglyMeasurable (fun ω => Real.exp |ω f|) (muGFF m).toMeasure :=
    (Real.continuous_exp.measurable.comp (continuous_abs.measurable.comp (WeakDual.eval_measurable
       f))).aestronglyMeasurable
  rcases eq_or_ne p 0 with rfl | hp_pos
  · exact memLp_zero_iff_aestronglyMeasurable.mpr h_aesm
  -- For 0 < p < ∞: exp(p|x|) ≤ exp(p²/(4α)) * exp(α x²) by Young's inequality.
  have h_exp_bound : ∀ x : ℝ, Real.exp (p.toReal * |x|) ≤
      Real.exp (p.toReal^2 / (4 * α)) * Real.exp (α * x^2) := fun x => by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (young_ineq p.toReal α hα_pos x)
  -- exp(p|ω f|) is integrable by domination.
  have h_exp_p_integrable : Integrable (fun ω => Real.exp (p.toReal * |ω f|)) (muGFF m).toMeasure
    := by
    have h_dom : Integrable (fun ω => Real.exp (p.toReal^2 / (4 * α)) * Real.exp (α * (ω f)^2))
        (muGFF m).toMeasure := by
      simpa only [distributionPairingCLM_apply, distributionPairing] using
        h_fernique.const_mul (Real.exp (p.toReal^2 / (4 * α)))
    apply h_dom.mono' ((Real.continuous_exp.measurable.comp (measurable_const.mul
      (continuous_abs.measurable.comp (WeakDual.eval_measurable f)))).aestronglyMeasurable)
    filter_upwards with ω
    simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      h_exp_bound (ω f)
  refine ⟨h_aesm, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp_pos hp]
  -- ‖exp(|x|)‖ₑ^p = exp(p|x|), reducing finiteness to h_exp_p_integrable.
  have h_eq : ∀ ω : FieldConfiguration,
      (‖Real.exp |ω f|‖ₑ : ENNReal) ^ p.toReal = ENNReal.ofReal (Real.exp (p.toReal * |ω f|)) := by
    intro ω
    rw [Real.enorm_eq_ofReal (Real.exp_pos _).le,
      ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg, ← Real.exp_mul]
    ring_nf
  simp_rw [h_eq]
  have h_fin := h_exp_p_integrable.hasFiniteIntegral
  rw [HasFiniteIntegral] at h_fin
  convert h_fin using 1
  exact lintegral_congr fun ω => by rw [Real.enorm_eq_ofReal (Real.exp_pos _).le]

/-- Integrability of exp(|ω f|) under the GFF measure.
    This is the L¹ special case of gff_exp_abs_pairing_memLp.
-/
lemma gff_exp_abs_pairing_integrable (f : TestFunction) :
    Integrable (fun ω : FieldConfiguration => Real.exp |ω f|) (muGFF m).toMeasure :=
  memLp_one_iff_integrable.mp (gff_exp_abs_pairing_memLp m f 1 ENNReal.one_ne_top)

/-- Product of exponentials of absolute pairings is in L².
    If we have k test functions g₁, ..., gₖ, then exp(∑ᵢ |ω gᵢ|) = ∏ᵢ exp(|ω gᵢ|).
    Each exp(|ω gᵢ|) ∈ L^(2k) by gff_exp_abs_pairing_memLp.
    By generalized Hölder (MemLp.prod'), a product of k functions in L^(2k) is in L².
-/
lemma gff_exp_abs_sum_memLp {ι : Type*} (s : Finset ι) (g : ι → TestFunction) :
    MemLp (fun ω : FieldConfiguration => Real.exp (∑ i ∈ s, |ω (g i)|)) 2 (muGFF m).toMeasure := by
  -- Rewrite exp(sum) as product of exp
  have h_eq : (fun ω : FieldConfiguration => Real.exp (∑ i ∈ s, |ω (g i)|)) =
              (fun ω : FieldConfiguration => ∏ i ∈ s, Real.exp |ω (g i)|) :=
    funext fun ω => Real.exp_sum s (fun i => |ω (g i)|)
  rw [h_eq]
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp [memLp_const]
  -- For nonempty s, each factor is in L^(2·card s); generalized Hölder gives L².
  have hk_ne_zero : (s.card : ENNReal) ≠ 0 := by simpa using (Finset.card_pos.mpr hs).ne'
  have hk_ne_top : (s.card : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top s.card
  have h_prod := MemLp.prod' (s := s) (p := fun _ => (2 * s.card : ℕ))
    (f := fun i (ω : FieldConfiguration) => Real.exp |ω (g i)|)
    (fun i _ => gff_exp_abs_pairing_memLp m (g i) (2 * s.card : ℕ) (ENNReal.natCast_ne_top _))
  -- The resulting exponent is (∑ i ∈ s, (2·card s)⁻¹)⁻¹ = (card s · (2·card s)⁻¹)⁻¹ = 2.
  convert h_prod using 1
  rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat, mul_comm (2 : ENNReal)]
  have h_inner : (s.card : ENNReal) * ((s.card : ENNReal) * 2)⁻¹ = 2⁻¹ := by
    rw [ENNReal.mul_inv (Or.inl hk_ne_zero) (Or.inl hk_ne_top), ← mul_assoc,
      ENNReal.mul_inv_cancel hk_ne_zero hk_ne_top, one_mul]
  rw [h_inner, inv_inv]

/-- The integral of ‖exp(I * distributionPairingℂReal ω f)‖ is finite for any
complex test function.
    This follows from the Gaussian exponential integrability applied to the imaginary part.
-/
lemma gff_integrand_norm_integrable (f : TestFunctionℂ) :
    Integrable (fun ω : FieldConfiguration =>
        ‖Complex.exp (Complex.I * distributionPairingℂReal ω f)‖)
      (muGFF m).toMeasure := by
  -- Rewrite the norm using our lemma
  simp_rw [norm_exp_I_distributionPairingℂ_real]
  -- This is exp(-(ω f_im)) which is integrable by gff_exp_neg_pairing_integrable
  exact gff_exp_neg_pairing_integrable m (complexTestFunctionDecompose f).2



/-- The GFF integrand is integrable for each z.
    This follows from the norm being exp(-(ω f_im)) which is integrable by
    Gaussian exponential integrability.
-/
theorem gff_integrand_integrable (n : ℕ) (J : Fin n → TestFunctionℂ) (z : Fin n → ℂ) :
    Integrable
      (fun ω : FieldConfiguration =>
        Complex.exp (Complex.I * distributionPairingℂReal ω (∑ i, z i • J i)))
      (muGFF m).toMeasure :=
  -- The norm is exp(-(ω f_im)) which is integrable
  (integrable_norm_iff (gff_integrand_measurable m n J z)).mp
    (gff_integrand_norm_integrable m (∑ i, z i • J i))

/-! ## Complex Characteristic Functional

The complex generating functional of the GFF equals exp(-½ C_ℂ(f,f)) where
C_ℂ(f,g) = ∫∫ f(x) C(x,y) g(y) is the complexified covariance bilinear form.

This follows from the bivariate Gaussian MGF: for (X,Y) = (ω(f_re), ω(f_im))
jointly Gaussian, E[exp(iX - Y)] = exp(½(-Var(X) - 2i Cov(X,Y) + Var(Y)))
which equals exp(-½ C_ℂ(f,f)).
-/

/-- The complex generating functional is analytic in a 1-parameter family.
    For fixed real f_re, f_im, the map t ↦ Z[toComplex f_re + t • toComplex f_im]
    is entire (analytic on all of ℂ).

    This follows from: for each ω, the integrand exp(i⟨ω,f_re⟩ + it⟨ω,f_im⟩) is
    entire in t; the modulus is bounded by exp(|Im(t)| · |⟨ω,f_im⟩|), which is
    integrable by Fernique's theorem (gaussianFreeField_pairing_memLp).
    Standard parameter-dependent holomorphy then gives analyticity of the integral.
-/
lemma gff_cf_slice_entire (f_re f_im : TestFunction) :
    AnalyticOnNhd ℂ (fun t : ℂ =>
      GJGeneratingFunctionalℂ (muGFF m) (toComplex f_re + t • toComplex f_im))
      Set.univ := by
  -- Abbreviations
  set a : FieldConfiguration → ℂ := fun ω => Complex.I * (ω f_re : ℂ)
  set b : FieldConfiguration → ℂ := fun ω => Complex.I * (ω f_im : ℂ)
  set F : ℂ → FieldConfiguration → ℂ := fun t ω => Complex.exp (a ω + t * b ω)
  -- Helper: Re(a(ω) + t * b(ω)) = -t.im * ω(f_im)
  have h_re_formula : ∀ ω t, (a ω + t * b ω).re = -t.im * ω f_im := fun ω t => by
    simp [a, b, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  -- Measurability helpers
  have h_eval_meas_re := WeakDual.eval_measurable f_re
  have h_eval_meas_im := WeakDual.eval_measurable f_im
  have h_ofReal_re : Measurable (fun ω : FieldConfiguration => (ω f_re : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp h_eval_meas_re
  have h_ofReal_im : Measurable (fun ω : FieldConfiguration => (ω f_im : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp h_eval_meas_im
  have h_a_meas : Measurable a := h_ofReal_re.const_mul _
  have h_b_meas : Measurable b := h_ofReal_im.const_mul _
  -- F(t, ·) is AEStronglyMeasurable
  have hF_meas : ∀ t, AEStronglyMeasurable (F t) (muGFF m).toMeasure := fun t =>
    (Complex.continuous_exp.measurable.comp
      (h_a_meas.add (h_b_meas.const_mul t))).aestronglyMeasurable
  -- Fernique domination: exp(c|ω f_im|) is integrable for any c ≥ 0
  have fernique_dom : ∀ (c : ℝ), 0 ≤ c →
      Integrable (fun ω => Real.exp (c * |ω f_im|)) (muGFF m).toMeasure := by
    intro c _
    obtain ⟨α, hα_pos, h_fernique⟩ := gaussianFreeField_pairing_expSq_integrable m f_im
    have h_dom : Integrable (fun ω => Real.exp (c ^ 2 / (4 * α) + α * (ω f_im) ^ 2))
        (muGFF m).toMeasure := by
      simpa only [distributionPairingCLM_apply, distributionPairing, ← Real.exp_add] using
        h_fernique.const_mul (Real.exp (c ^ 2 / (4 * α)))
    apply h_dom.mono
      (Real.continuous_exp.measurable.comp
        (measurable_const.mul (continuous_abs.measurable.comp h_eval_meas_im))
        |>.aestronglyMeasurable)
    filter_upwards with ω
    simp only [Real.norm_eq_abs, Function.comp_def, abs_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_exp.mpr (young_ineq c α hα_pos (ω f_im))
  -- Step 1: rewrite the goal to use ∫ F t ω dμ via AnalyticOnNhd.congr
  -- The generating functional equals the integral of F
  have h_eq : Set.EqOn
      (fun t => ∫ ω, F t ω ∂(muGFF m).toMeasure)
      (fun t => GJGeneratingFunctionalℂ (muGFF m) (toComplex f_re + t • toComplex f_im))
      Set.univ := by
    intro t _
    simp only [GJGeneratingFunctionalℂ]
    congr 1
    funext ω
    simp only [F, a, b]
    congr 1
    have h1 := pairing_linear_combo ω (toComplex f_re) (toComplex f_im) 1 t
    simp only [one_smul, one_mul, distributionPairingℂ_real_toComplex, distributionPairing] at h1
    rw [h1]; ring
  -- It suffices to prove ∫ F is analytic
  suffices h_analytic : AnalyticOnNhd ℂ (fun t => ∫ ω, F t ω ∂(muGFF m).toMeasure) Set.univ from
    h_analytic.congr isOpen_univ h_eq
  -- Step 2: Differentiable ℂ → AnalyticOnNhd (Goursat's theorem for ℂ → ℂ)
  suffices h_diff : Differentiable ℂ (fun t => ∫ ω, F t ω ∂(muGFF m).toMeasure) by
    intro t₀ _; exact h_diff.analyticAt t₀
  -- For each t₀, apply hasFDerivAt_integral_of_dominated_of_fderiv_le
  intro t₀
  -- d/dt F(t,ω) = b(ω) * F(t,ω)
  have h_hasderiv : ∀ ω t, HasDerivAt (F · ω) (b ω * F t ω) t := by
    intro ω t
    have h1 : HasDerivAt (fun t => a ω + t * b ω) (b ω) t := by
      simpa using (hasDerivAt_mul_const (b ω)).const_add (a ω)
    rw [show b ω * F t ω = Complex.exp (a ω + t * b ω) * b ω from mul_comm _ _]
    exact h1.cexp
  set s := Metric.ball t₀ 1
  -- |t.im| ≤ |t₀.im| + 1 for t ∈ B(t₀, 1)
  have h_im_bound : ∀ t ∈ s, |t.im| ≤ |t₀.im| + 1 := by
    intro t ht
    have h_dist := Metric.mem_ball.mp ht
    rw [dist_eq_norm] at h_dist
    have h1 := Complex.abs_im_le_norm (t - t₀)
    simp only [Complex.sub_im] at h1
    linarith [abs_sub_abs_le_abs_sub t.im t₀.im]
  -- Integrability of F(t₀, ·)
  have hF_int : Integrable (F t₀) (muGFF m).toMeasure := by
    apply (fernique_dom (|t₀.im|) (abs_nonneg _)).mono (hF_meas t₀)
    filter_upwards with ω
    simp only [F, Complex.norm_exp, h_re_formula]
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    refine Real.exp_le_exp.mpr ?_
    rw [neg_mul, ← abs_mul]
    exact neg_le_abs _
  -- Frechet derivative
  have h_fderiv : ∀ ω t, HasFDerivAt (F · ω)
      (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (b ω * F t ω)) t :=
    fun ω t => (h_hasderiv ω t).hasFDerivAt
  -- Derivative measurability at t₀
  have hF'_meas : AEStronglyMeasurable
      (fun ω => ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (b ω * F t₀ ω))
      (muGFF m).toMeasure :=
    ((ContinuousLinearMap.smulRightL ℂ ℂ ℂ (1 : ℂ →L[ℂ] ℂ)).continuous.measurable.comp
      (h_b_meas.mul (Complex.continuous_exp.measurable.comp
        (h_a_meas.add (h_b_meas.const_mul t₀))))).aestronglyMeasurable
  -- Bound for derivative norm
  set bound : FieldConfiguration → ℝ := fun ω => |ω f_im| * Real.exp ((|t₀.im| + 1) * |ω f_im|)
  -- Fderiv bound on B(t₀, 1)
  have h_fderiv_bound : ∀ᵐ ω ∂(muGFF m).toMeasure, ∀ t ∈ s,
      ‖ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (b ω * F t ω)‖ ≤ bound ω := by
    filter_upwards with ω t ht
    rw [ContinuousLinearMap.norm_smulRight_apply, norm_one, one_mul]
    calc ‖b ω * F t ω‖
        = ‖b ω‖ * ‖F t ω‖ := norm_mul _ _
      _ = |ω f_im| * Real.exp ((a ω + t * b ω).re) := by
          simp only [b, F, Complex.norm_exp, Complex.norm_mul, Complex.norm_I,
            one_mul, Complex.norm_real, Real.norm_eq_abs]
      _ = |ω f_im| * Real.exp (-t.im * ω f_im) := by rw [h_re_formula]
      _ ≤ |ω f_im| * Real.exp ((|t₀.im| + 1) * |ω f_im|) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          refine Real.exp_le_exp.mpr (le_trans ?_
            (mul_le_mul_of_nonneg_right (h_im_bound t ht) (abs_nonneg _)))
          rw [neg_mul, ← abs_mul]
          exact neg_le_abs _
  -- Bound integrability via Fernique
  have h_bound_integrable : Integrable bound (muGFF m).toMeasure := by
    set c := |t₀.im| + 1
    -- bound(ω) = |ω f_im| * exp(c|ω f_im|) ≤ exp((c+1)|ω f_im|) since |x| ≤ exp(|x|)
    apply (fernique_dom (c + 1) (by positivity)).mono
    · exact ((continuous_abs.measurable.comp h_eval_meas_im).aestronglyMeasurable.mul
        ((Real.continuous_exp.measurable.comp
          (measurable_const.mul (continuous_abs.measurable.comp
             h_eval_meas_im))).aestronglyMeasurable))
    · filter_upwards with ω
      simp only [bound, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_nonneg _)),
        abs_of_nonneg (Real.exp_nonneg _)]
      calc |ω f_im| * Real.exp (c * |ω f_im|)
          ≤ Real.exp |ω f_im| * Real.exp (c * |ω f_im|) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
            calc |ω f_im| ≤ |ω f_im| + 1 := by linarith
              _ ≤ Real.exp |ω f_im| := Real.add_one_le_exp _
        _ = Real.exp ((c + 1) * |ω f_im|) := by rw [← Real.exp_add]; ring_nf
  -- Apply parametric integral differentiation
  exact (hasFDerivAt_integral_of_dominated_of_fderiv_le
    (Metric.ball_mem_nhds t₀ one_pos)
    (Filter.Eventually.of_forall hF_meas) hF_int hF'_meas
    h_fderiv_bound h_bound_integrable
    (by filter_upwards with ω t ht; exact h_fderiv ω t)).differentiableAt

/-- The complex characteristic functional of the GFF.

    For any complex test function f:
    Z[f] = E[exp(i⟨ω,f⟩_ℂ)] = exp(-½ C_ℂ(f, f))

    Proved by 1-parameter analytic continuation: decompose f = f_re + I·f_im,
    show the generating functional and Gaussian formula agree on ℝ (from
    `gff_real_characteristic`), extend to ℂ via the identity theorem.
-/
theorem gff_complex_CF_covariance (f : TestFunctionℂ) :
    GJGeneratingFunctionalℂ (muGFF m) f =
    cexp (-(1/2 : ℂ) * freeCovarianceℂBilinear m f f) := by
  -- Decompose f = toComplex f_re + I • toComplex f_im
  let f_re := (complexTestFunctionDecompose f).1
  let f_im := (complexTestFunctionDecompose f).2
  have hf : f = toComplex f_re + Complex.I • toComplex f_im := by
    ext x
    simpa [f_re, f_im, toComplex_apply, smul_eq_mul, complexTestFunctionDecompose]
      using complex_testfunction_decompose_recompose f x
  -- Define 1-parameter families: L(t) = Z[f_re + t·f_im], R(t) = exp(-½ Q(t))
  let L : ℂ → ℂ := fun t =>
    GJGeneratingFunctionalℂ (muGFF m) (toComplex f_re + t • toComplex f_im)
  let R : ℂ → ℂ := fun t =>
    cexp (-(1/2 : ℂ) * ((freeCovarianceFormR m f_re f_re : ℂ) +
      2 * t * (freeCovarianceFormR m f_re f_im : ℂ) +
      t ^ 2 * (freeCovarianceFormR m f_im f_im : ℂ)))
  -- Step 1: L and R agree on ℝ
  have h_agree : ∀ t : ℝ, L (t : ℂ) = R (t : ℂ) := by
    intro t
    simp only [L, R]
    have h_arg : toComplex f_re + (t : ℂ) • toComplex f_im = toComplex (f_re + t • f_im) := by
      ext x; simp [toComplex_apply]
    rw [h_arg, GJGeneratingFunctionalℂ_toComplex, gff_real_characteristic m]
    congr 1; congr 1
    have h_expand : freeCovarianceFormR m (f_re + t • f_im) (f_re + t • f_im)
        = freeCovarianceFormR m f_re f_re + 2 * t * freeCovarianceFormR m f_re f_im
          + t ^ 2 * freeCovarianceFormR m f_im f_im := by
      rw [freeCovarianceFormR_add_left, freeCovarianceFormR_add_right,
          freeCovarianceFormR_add_right,
          freeCovarianceFormR_smul_left, freeCovarianceFormR_smul_right,
          freeCovarianceFormR_smul_left, freeCovarianceFormR_smul_right,
          freeCovarianceFormR_symm m f_im f_re]
      ring
    rw [h_expand]; push_cast; ring
  -- Step 2: R is entire (exp of quadratic polynomial in t)
  have hR_an : AnalyticOnNhd ℂ R Set.univ := by
    apply AnalyticOnNhd.cexp
    apply AnalyticOnNhd.mul analyticOnNhd_const
    refine AnalyticOnNhd.add (AnalyticOnNhd.add analyticOnNhd_const ?_)
      (((analyticOnNhd_id (𝕜 := ℂ)).pow 2).mul analyticOnNhd_const)
    -- 2 * t * Q_ri is linear in t
    have : AnalyticOnNhd ℂ (fun t : ℂ =>
        (2 * (freeCovarianceFormR m f_re f_im : ℂ)) * t) Set.univ :=
      AnalyticOnNhd.mul analyticOnNhd_const analyticOnNhd_id
    have heq : (fun t : ℂ => 2 * t * (freeCovarianceFormR m f_re f_im : ℂ))
        = (fun t : ℂ => (2 * (freeCovarianceFormR m f_re f_im : ℂ)) * t) := by
      funext t; ring
    rw [heq]; exact this
  -- Step 3: L is entire (from parameter-dependent holomorphy)
  have hL_an : AnalyticOnNhd ℂ L Set.univ := gff_cf_slice_entire m f_re f_im
  -- Step 4: Identity theorem -- L = R on all of ℂ
  -- ℝ has accumulation points in ℂ, so agreement on ℝ forces global agreement.
  have h_eq : L = R := by
    apply AnalyticOnNhd.eq_of_frequently_eq hL_an hR_an (z₀ := 0)
    simp only [Filter.Frequently]
    intro hU
    rw [Filter.Eventually, mem_nhdsWithin] at hU
    obtain ⟨V, hV_open, h0_in_V, hV_sub⟩ := hU
    obtain ⟨ε, hε_pos, hε_ball⟩ := Metric.isOpen_iff.mp hV_open 0 h0_in_V
    -- ε/2 is a nonzero real in V ∩ {0}ᶜ where L = R, contradicting hU
    have h_half_pos : (0 : ℝ) < ε / 2 := half_pos hε_pos
    have h_mem_V : ((ε / 2 : ℝ) : ℂ) ∈ V := hε_ball (by
      simp only [Metric.mem_ball, Complex.dist_eq, sub_zero, Complex.norm_real]
      rw [Real.norm_eq_abs, abs_of_pos h_half_pos]
      linarith)
    have h_ne : ((ε / 2 : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]; linarith
    exact hV_sub ⟨h_mem_V, h_ne⟩ (h_agree (ε / 2))
  -- Step 5: Evaluate at t = I
  have h_eval : L Complex.I = R Complex.I := congrFun h_eq Complex.I
  -- Step 6: Relate L(I) to LHS and R(I) to RHS
  have h_LHS : GJGeneratingFunctionalℂ (muGFF m) f = L Complex.I := by
    simp only [L]; congr 1
  have h_RHS : cexp (-(1/2 : ℂ) * freeCovarianceℂBilinear m f f) = R Complex.I := by
    simp only [R]; congr 1; congr 1
    -- Expand C_ℂ(f, f) using bilinearity and agrees_on_reals
    conv_lhs => rw [hf]
    rw [freeCovarianceℂ_bilinear_add_left, freeCovarianceℂ_bilinear_add_right,
        freeCovarianceℂ_bilinear_add_right]
    simp only [freeCovarianceℂ_bilinear_smul_left, freeCovarianceℂ_bilinear_smul_right]
    rw [freeCovarianceℂ_bilinear_agrees_on_reals m f_re f_re,
        freeCovarianceℂ_bilinear_agrees_on_reals m f_re f_im,
        freeCovarianceℂ_bilinear_agrees_on_reals m f_im f_re,
        freeCovarianceℂ_bilinear_agrees_on_reals m f_im f_im,
        freeCovarianceFormR_symm m f_im f_re]
    ring
  rw [h_LHS, h_eval, ← h_RHS]

/-! ## Bilinear Expansion for Finite Sums

Using the ℂ-bilinearity of `freeCovarianceℂBilinear`, we expand
C_ℂ(∑ᵢ zᵢ Jᵢ, ∑ⱼ zⱼ Jⱼ) = ∑ᵢ ∑ⱼ zᵢ zⱼ C_ℂ(Jᵢ, Jⱼ).
-/

/-- C_ℂ(f, 0) = 0, derived from smul_right with c = 0. -/
private lemma freeCovarianceℂ_bilinear_zero_right (f : TestFunctionℂ) :
    freeCovarianceℂBilinear m f 0 = 0 := by
  simpa using freeCovarianceℂ_bilinear_smul_right m (0 : ℂ) f (0 : TestFunctionℂ)

/-- C_ℂ(0, g) = 0, derived from smul_left with c = 0. -/
private lemma freeCovarianceℂ_bilinear_zero_left (g : TestFunctionℂ) :
    freeCovarianceℂBilinear m 0 g = 0 := by
  simpa using freeCovarianceℂ_bilinear_smul_left m (0 : ℂ) (0 : TestFunctionℂ) g

/-- Right linearity over finite sums for the complexified covariance. -/
private lemma freeCovarianceℂ_sum_right (f : TestFunctionℂ)
    (s : Finset (Fin n)) (z : Fin n → ℂ) (J : Fin n → TestFunctionℂ) :
    freeCovarianceℂBilinear m f (∑ i ∈ s, z i • J i) =
    ∑ i ∈ s, z i * freeCovarianceℂBilinear m f (J i) := by
  induction s using Finset.cons_induction with
  | empty => simp [freeCovarianceℂ_bilinear_zero_right]
  | cons a s ha ih =>
    rw [Finset.sum_cons, freeCovarianceℂ_bilinear_add_right,
        freeCovarianceℂ_bilinear_smul_right, ih, Finset.sum_cons]

/-- Left linearity over finite sums for the complexified covariance. -/
private lemma freeCovarianceℂ_sum_left
    (s : Finset (Fin n)) (z : Fin n → ℂ) (J : Fin n → TestFunctionℂ)
    (g : TestFunctionℂ) :
    freeCovarianceℂBilinear m (∑ i ∈ s, z i • J i) g =
    ∑ i ∈ s, z i * freeCovarianceℂBilinear m (J i) g := by
  induction s using Finset.cons_induction with
  | empty => simp [freeCovarianceℂ_bilinear_zero_left]
  | cons a s ha ih =>
    rw [Finset.sum_cons, freeCovarianceℂ_bilinear_add_left,
        freeCovarianceℂ_bilinear_smul_left, ih, Finset.sum_cons]

/-- Full bilinear expansion of C_ℂ(∑ zᵢ Jᵢ, ∑ zⱼ Jⱼ) as a finite double sum. -/
theorem freeCovarianceℂ_bilinear_sum_expansion {n : ℕ}
    (J : Fin n → TestFunctionℂ) (z : Fin n → ℂ) :
    freeCovarianceℂBilinear m (∑ i, z i • J i) (∑ j, z j • J j) =
    ∑ i : Fin n, ∑ j : Fin n,
      z i * z j * freeCovarianceℂBilinear m (J i) (J j) := by
  rw [freeCovarianceℂ_sum_left m Finset.univ z J]
  congr 1; ext i
  rw [freeCovarianceℂ_sum_right m (J i) Finset.univ z J]
  rw [Finset.mul_sum]; congr 1; ext j; ring

/-- The generating functional for ∑ᵢ zᵢ Jᵢ equals exp of a finite quadratic form. -/
theorem gff_generating_eq_exp_quadratic {n : ℕ}
    (J : Fin n → TestFunctionℂ) (z : Fin n → ℂ) :
    GJGeneratingFunctionalℂ (muGFF m) (∑ i, z i • J i) =
    cexp (-(1/2 : ℂ) * ∑ i : Fin n, ∑ j : Fin n,
      z i * z j * freeCovarianceℂBilinear m (J i) (J j)) := by
  rw [gff_complex_CF_covariance, freeCovarianceℂ_bilinear_sum_expansion]

/-! ## Analyticity of exp(finite quadratic form)

A finite quadratic form z ↦ ∑ᵢⱼ Aᵢⱼ zᵢ zⱼ is a polynomial, hence analytic.
Composing with exp preserves analyticity.
-/

/-- A finite quadratic form ∑ᵢⱼ Aᵢⱼ zᵢ zⱼ is analytic (it's a polynomial). -/
theorem analyticOn_finite_quadratic {n : ℕ} (A : Fin n → Fin n → ℂ) :
    AnalyticOn ℂ (fun z : Fin n → ℂ =>
      ∑ i : Fin n, ∑ j : Fin n, z i * z j * A i j) Set.univ := by
  have h_fn_eq : (fun z : Fin n → ℂ => ∑ i : Fin n, ∑ j : Fin n, z i * z j * A i j) =
      ∑ i : Fin n, ∑ j : Fin n, (fun z : Fin n → ℂ => z i * z j * A i j) := by
    ext z; simp [Finset.sum_apply]
  rw [h_fn_eq]
  exact Finset.analyticOn_sum _ fun i _ =>
    Finset.analyticOn_sum _ fun j _ =>
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i).analyticOn _|>.mul
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j).analyticOn _)).mul
        analyticOn_const

/-- The Gaussian Free Field satisfies the OS0 Analyticity axiom.

    **Direct proof** from the covariance structure: Z[f] = exp(-½ C_ℂ(f,f))
    and C_ℂ is ℂ-bilinear, so Z[∑ zᵢ Jᵢ] = exp(quadratic polynomial in z).
-/
theorem gaussianFreeField_satisfies_OS0 : os0Analyticity (muGFF m) := by
  intro n J
  -- Step 1: Rewrite using the covariance quadratic form
  have h_eq : ∀ z : Fin n → ℂ,
      GJGeneratingFunctionalℂ (muGFF m) (∑ i, z i • J i) =
      cexp (-(1/2 : ℂ) * ∑ i : Fin n, ∑ j : Fin n,
        z i * z j * freeCovarianceℂBilinear m (J i) (J j)) :=
    fun z => gff_generating_eq_exp_quadratic m J z
  -- Step 2: The quadratic form is analytic
  have h_analytic : AnalyticOn ℂ (fun z : Fin n → ℂ =>
      cexp (-(1/2 : ℂ) * ∑ i : Fin n, ∑ j : Fin n,
        z i * z j * freeCovarianceℂBilinear m (J i) (J j))) Set.univ :=
    (analyticOn_const.mul (analyticOn_finite_quadratic
      (fun i j => freeCovarianceℂBilinear m (J i) (J j)))).cexp
  -- Step 3: Conclude by pointwise equality
  exact h_analytic.congr (fun z _ => (h_eq z))

end QFT
