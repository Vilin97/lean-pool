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

variable (m : ℝ) [Fact (0 < m)]

/-- The complex pairing is continuous in ω.
    This follows from the continuity of the evaluation map on WeakDual.
-/
theorem distributionPairingℂ_real_continuous (f : TestFunctionℂ) :
    Continuous (fun ω : FieldConfiguration => distributionPairingℂReal ω f) := by
  -- distributionPairingℂReal ω f = ω f_re + I * ω f_im
  -- where f_re = schwartzCompCLM f reCLM and f_im = schwartzCompCLM f imCLM
  simp only [distributionPairingℂReal, complexTestFunctionDecompose]
  -- Now we need: Continuous (ω ↦ ↑(ω (schwartzCompCLM f reCLM)) + I * ↑(ω (schwartzCompCLM f
  -- imCLM)))
  -- Each evaluation ω ↦ ω g is continuous by WeakDual.eval_continuous
  have h_re : Continuous (fun ω : FieldConfiguration => (ω (schwartzCompCLM f Complex.reCLM) :
    ℂ)) :=
    Complex.continuous_ofReal.comp (WeakDual.eval_continuous _)
  have h_im : Continuous (fun ω : FieldConfiguration => (ω (schwartzCompCLM f Complex.imCLM) :
    ℂ)) :=
    Complex.continuous_ofReal.comp (WeakDual.eval_continuous _)
  -- The full pairing is a continuous combination
  exact h_re.add (continuous_const.mul h_im)

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
  -- The function is exp ∘ (I * pairing ∘ linear_combination)
  -- Each component is analytic, and composition of analytic functions is analytic
  -- exp is entire, so we need to show the argument is analytic
  apply AnalyticAt.cexp
  -- Now show I * distributionPairingℂReal ω (∑ i, z i • J i) is analytic in z
  apply AnalyticAt.mul
  · -- Complex.I is constant, hence analytic
    exact analyticAt_const
  · -- distributionPairingℂReal ω (∑ i, z i • J i) is analytic in z
    -- The function z ↦ distributionPairingℂReal ω (∑ i, z i • J i) is linear in z
    -- because distributionPairingℂReal is linear in its test function argument
    -- and the sum is linear in z.
    -- A linear function from a finite-dimensional space to ℂ is analytic.
    -- The function is: z ↦ ∑ i, z i * (distributionPairingℂReal ω (J i))
    -- which is a finite sum of z i times constants.
    -- Rewrite using linearity of distributionPairingℂReal
    have h_linear : ∀ z : Fin n → ℂ, distributionPairingℂReal ω (∑ i, z i • J i) =
        ∑ i, z i * distributionPairingℂReal ω (J i) := fun z => by
      -- distributionPairingℂReal is linear in the test function
      -- Use pairing_linear_combo: pairing(t•f + s•g) = t * pairing(f) + s * pairing(g)
      -- First establish the basic linearity properties
      have h_add : ∀ f g : TestFunctionℂ, distributionPairingℂReal ω (f + g) =
          distributionPairingℂReal ω f + distributionPairingℂReal ω g := fun f g => by
        have := pairing_linear_combo ω f g 1 1
        simpa only [one_smul, one_mul] using this
      have h_smul : ∀ (c : ℂ) (f : TestFunctionℂ), distributionPairingℂReal ω (c • f) =
          c * distributionPairingℂReal ω f := fun c f => by
        have := pairing_linear_combo ω f 0 c 0
        simpa only [zero_smul, add_zero, zero_mul] using this
      have h_zero : distributionPairingℂReal ω 0 = 0 := by
        have := pairing_linear_combo ω 0 0 0 0
        simpa only [zero_smul, zero_add, zero_mul, add_zero] using this
      -- Use Finset.induction_on for the sum
      have h_gen : ∀ (s : Finset (Fin n)),
          distributionPairingℂReal ω (∑ i ∈ s, z i • J i) =
          ∑ i ∈ s, z i * distributionPairingℂReal ω (J i) := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp [h_zero]
        | insert i s hi ih =>
          rw [Finset.sum_insert hi, Finset.sum_insert hi]
          rw [h_add, h_smul, ih]
      exact h_gen Finset.univ
    -- Now show ∑ i, z i * c_i is analytic (it's a polynomial)
    simp_rw [h_linear]
    -- Use Finset.analyticAt_fun_sum: if each f_i is analytic, then z ↦ ∑ i, f_i z is analytic
    apply Finset.analyticAt_fun_sum
    intro i _
    -- Show z ↦ z i * c_i is analytic
    apply AnalyticAt.mul
    · -- z ↦ z i is a continuous linear map (projection), hence analytic
      exact ContinuousLinearMap.analyticAt (ContinuousLinearMap.proj (R := ℂ) i) z₀
    · -- c_i = distributionPairingℂReal ω (J i) is a constant function in z
      exact analyticAt_const

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
  -- Use exponential square integrability (Fernique)
  -- For any α > 0, exp(α x²) is integrable, and exp(-x) ≤ exp(α x² + 1/(4α))
  obtain ⟨α, hα_pos, h_integ⟩ := gaussianFreeField_pairing_expSq_integrable m f
  -- exp(-x) ≤ exp(α x² + 1/(4α)) by completing the square: -x = -(√α x - 1/(2√α))² + α x² + 1/(4α)
  have h_bound : ∀ x : ℝ, Real.exp (-x) ≤ Real.exp (1 / (4 * α)) * Real.exp (α * x^2) := fun x => by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    -- Need: -x ≤ 1/(4α) + α x²
    -- This is equivalent to: α x² + x + 1/(4α) ≥ 0
    -- Which is (√α x + 1/(2√α))² ≥ 0
    have h : α * x^2 + x + 1 / (4 * α) = (Real.sqrt α * x + 1 / (2 * Real.sqrt α))^2 := by
      have hα_sqrt : Real.sqrt α > 0 := Real.sqrt_pos.mpr hα_pos
      have hα_ne : Real.sqrt α ≠ 0 := ne_of_gt hα_sqrt
      field_simp
      rw [Real.sq_sqrt (le_of_lt hα_pos)]
      ring
    linarith [sq_nonneg (Real.sqrt α * x + 1 / (2 * Real.sqrt α))]
  -- The dominating function g(ω) = exp(1/(4α)) * exp(α (ω f)²) is integrable
  have h_dom_integrable : Integrable
      (fun ω => Real.exp (1 / (4 * α)) * Real.exp (α * (distributionPairingCLM f ω)^2))
      (muGFF m).toMeasure := h_integ.const_mul (Real.exp (1 / (4 * α)))
  -- exp(-ω f) is measurable
  have h_meas : AEStronglyMeasurable (fun ω : FieldConfiguration => Real.exp (-(ω f)))
      (muGFF m).toMeasure :=
    (Real.continuous_exp.measurable.comp (measurable_neg.comp (WeakDual.eval_measurable
       f))).aestronglyMeasurable
  -- Pointwise bound: ‖exp(-ω f)‖ ≤ exp(1/(4α)) * exp(α (ω f)²)
  have h_ae_bound : ∀ᵐ ω ∂(muGFF m).toMeasure,
      ‖Real.exp (-(ω f))‖ ≤ Real.exp (1 / (4 * α)) * Real.exp (α * (distributionPairingCLM f ω)^2)
        := by
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    simp only [distributionPairingCLM_apply, distributionPairing]
    exact h_bound (ω f)
  -- Apply Integrable.mono'
  exact h_dom_integrable.mono' h_meas h_ae_bound

/-- exp(|ω f|) is in L^2 (and in fact all L^p) under the GFF measure.
    This follows from Fernique's theorem: if exp(α x²) is integrable, then exp(|x|)^p is integrable
    for all p < ∞ because |x|^p ≤ C_p * exp(ε x²) for small ε.
-/
lemma gff_exp_abs_pairing_memLp (f : TestFunction) (p : ENNReal) (hp : p ≠ ⊤) :
    MemLp (fun ω : FieldConfiguration => Real.exp |ω f|) p (muGFF m).toMeasure := by
  -- By Fernique, ∃ α > 0 such that exp(α x²) is integrable
  obtain ⟨α, hα_pos, h_fernique⟩ := gaussianFreeField_pairing_expSq_integrable m f
  -- For any p < ∞, we use exp(|x|)^p = exp(p|x|) ≤ exp(p²/(4α)) * exp(α x²)
  -- because p|x| ≤ p²/(4α) + α x² by AM-GM: 2√(p|x| * α x²) ≤ p|x| + α x²
  -- Actually, more directly: p|x| = (p/(2√α)) * (2√α |x|) ≤ p²/(4α) + α x²
  -- So exp(p|x|) ≤ exp(p²/(4α)) * exp(α x²)
  -- Thus ∫ exp(p|x|)^1 ≤ C * ∫ exp(α x²) < ∞
  -- For the formal proof, we establish L¹ first (which we already have) then bootstrap
  -- The MemLp condition requires showing ∫ ‖exp(|ω f|)‖^p < ∞
  -- Case split on whether p = 0 (trivial) or p > 0
  rcases eq_or_ne p 0 with rfl | hp_pos
  · exact memLp_zero_iff_aestronglyMeasurable.mpr
      (Real.continuous_exp.measurable.comp (continuous_abs.measurable.comp
         (WeakDual.eval_measurable f))).aestronglyMeasurable
  -- For 0 < p < ∞, we need ∫ (exp |x|)^p dμ < ∞
  -- (exp |x|)^p = exp(p * |x|), and for p finite this is bounded by C * exp(α x²)
  -- The detailed proof uses Young's inequality: p|x| ≤ p²/(4α) + α x²
  -- Here we use the fact that for any test function, linear functionals on Gaussian
  -- measures have all moments finite, so any polynomial growth times exponential decay
  -- is integrable. We axiomatize this as part of the Fernique condition.
  -- For now, use the fact that we have L¹ integrability and the function is AE bounded
  -- by a multiple of exp(α x²) which is integrable
  have h_aesm : AEStronglyMeasurable (fun ω => Real.exp |ω f|) (muGFF m).toMeasure :=
    (Real.continuous_exp.measurable.comp (continuous_abs.measurable.comp (WeakDual.eval_measurable
       f))).aestronglyMeasurable
  -- The core estimate: exp(p|x|) ≤ C * exp(α x²) for some C depending on p and α
  -- This follows from: p|x| ≤ p²/(4α) + α x² (Young's inequality)
  -- So exp(p|x|) ≤ exp(p²/(4α)) * exp(α x²)
  -- The proof: ‖exp(|x|)‖^p = exp(p.toReal * |x|) ≤ C * exp(α x²) for Young's constant C
  -- Therefore ∫ ‖exp(|x|)‖^p dμ ≤ C * ∫ exp(α x²) dμ < ∞
  -- Young's inequality: for α > 0 and any real r, we have r|x| ≤ r²/(4α) + α x²
  -- This follows from (r/(2√α) - √α|x|)² ≥ 0
  have h_young : ∀ x : ℝ, p.toReal * |x| ≤ p.toReal^2 / (4 * α) + α * x^2 := fun x => by
    have hα_ne : α ≠ 0 := ne_of_gt hα_pos
    have h_sqrt_pos : Real.sqrt α > 0 := Real.sqrt_pos.mpr hα_pos
    have h_sqrt_sq : Real.sqrt α ^ 2 = α := Real.sq_sqrt (le_of_lt hα_pos)
    -- Let a = p/(2√α), b = √α|x|. Then (a-b)² ≥ 0 gives a² + b² ≥ 2ab = p|x|
    have ha : p.toReal / (2 * Real.sqrt α) = p.toReal / 2 / Real.sqrt α := by ring
    have hb_sq : (Real.sqrt α * |x|)^2 = α * x^2 := by rw [mul_pow, h_sqrt_sq, sq_abs]
    have ha_sq : (p.toReal / (2 * Real.sqrt α))^2 = p.toReal^2 / (4 * α) := by
      rw [div_pow, mul_pow, h_sqrt_sq]; ring
    have hab : 2 * (p.toReal / (2 * Real.sqrt α)) * (Real.sqrt α * |x|) = p.toReal * |x| := by
      field_simp
    have h_sq := sq_nonneg (p.toReal / (2 * Real.sqrt α) - Real.sqrt α * |x|)
    calc p.toReal * |x| = 2 * (p.toReal / (2 * Real.sqrt α)) * (Real.sqrt α * |x|) := hab.symm
      _ ≤ (p.toReal / (2 * Real.sqrt α))^2 + (Real.sqrt α * |x|)^2 := by nlinarith [h_sq]
      _ = p.toReal^2 / (4 * α) + α * x^2 := by rw [ha_sq, hb_sq]
  -- Exponential bound: exp(p|x|) ≤ exp(p²/(4α)) * exp(α x²)
  have h_exp_bound : ∀ x : ℝ,
      Real.exp (p.toReal * |x|) ≤ Real.exp (p.toReal^2 / (4 * α)) * Real.exp (α * x^2) := fun x =>
        by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (h_young x)
  -- The constant C = exp(p²/(4α))
  let C := Real.exp (p.toReal^2 / (4 * α))
  -- The dominating function C * exp(α x²) is integrable
  have h_dom : Integrable (fun ω => C * Real.exp (α * (ω f)^2)) (muGFF m).toMeasure := by
    have h_const_mul : Integrable (fun ω => C * Real.exp (α * (distributionPairingCLM f ω)^2))
      (muGFF m).toMeasure := by
      exact h_fernique.const_mul C
    simp only [distributionPairingCLM_apply, distributionPairing] at h_const_mul
    exact h_const_mul
  -- For the MemLp construction, we need snorm to be finite
  -- snorm f p μ = (∫ ‖f‖^p)^(1/p) for p ∈ (0, ∞)
  -- ‖exp(|x|)‖^p = exp(|x|)^p = exp(p * |x|)
  -- The key: exp(p|ω f|) ≤ C * exp(α (ω f)²) and RHS is integrable
  have h_norm_pow_bound : ∀ ω : FieldConfiguration,
      Real.exp (p.toReal * |ω f|) ≤ C * Real.exp (α * (ω f)^2) := fun ω => by
    have h1 := h_exp_bound (ω f)
    exact h1
  -- Integrability of exp(p|ω f|) follows from domination
  have h_exp_p_integrable : Integrable (fun ω => Real.exp (p.toReal * |ω f|)) (muGFF m).toMeasure
    := by
    have h_meas : AEStronglyMeasurable (fun ω => Real.exp (p.toReal * |ω f|)) (muGFF m).toMeasure :=
      (Real.continuous_exp.measurable.comp (measurable_const.mul (continuous_abs.measurable.comp
        (WeakDual.eval_measurable f)))).aestronglyMeasurable
    -- Use Integrable.mono': if g is integrable and ‖f‖ ≤ g a.e., then f is integrable
    apply h_dom.mono' h_meas
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact h_norm_pow_bound ω
  -- Now we construct MemLp using the snorm condition
  -- For 0 < p < ∞, MemLp f p μ iff AEStronglyMeasurable f μ ∧ snorm f p μ < ⊤
  -- snorm f p μ = (∫ ‖f‖^p.toReal)^(1/p.toReal) when 0 < p < ⊤
  -- The key observation: ‖exp(|x|)‖^(p.toReal) = exp(p.toReal * |x|)
  have h_norm_rpow : ∀ x : ℝ, ‖Real.exp |x|‖ ^ p.toReal = Real.exp (p.toReal * |x|) := fun x => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [← Real.exp_mul]
    congr 1
    ring
  -- Convert integrability of exp(p|x|) to eLpNorm bound
  -- Using: eLpNorm f p μ < ∞ ↔ ∫⁻ ‖f‖ₑ^p ∂μ < ∞
  have h_eLpNorm_lt : eLpNorm (fun ω => Real.exp |ω f|) p (muGFF m).toMeasure < ⊤ := by
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp_pos hp]
    -- Need: ∫⁻ ‖exp(|ω f|)‖ₑ^p < ⊤
    -- Since ‖exp(|x|)‖ₑ = exp(|x|), we have ‖exp(|x|)‖ₑ^p = exp(p|x|)
    -- and exp(p|x|) is integrable by h_exp_p_integrable
    have h_eq : ∀ ω : FieldConfiguration,
        (‖Real.exp |ω f|‖ₑ : ENNReal) ^ p.toReal = ENNReal.ofReal (Real.exp (p.toReal * |ω f|)) :=
           by
      intro ω
      have h_pos : 0 < Real.exp |ω f| := Real.exp_pos _
      rw [Real.enorm_eq_ofReal (le_of_lt h_pos)]
      rw [ENNReal.ofReal_rpow_of_nonneg (le_of_lt h_pos) (ENNReal.toReal_nonneg)]
      congr 1
      -- exp(|x|)^p = exp(p * |x|)
      rw [← Real.exp_mul]
      ring_nf
    simp_rw [h_eq]
    -- Use that integrability implies lintegral is finite
    have h_fin := h_exp_p_integrable.hasFiniteIntegral
    rw [HasFiniteIntegral] at h_fin
    convert h_fin using 1
    apply lintegral_congr
    intro ω
    rw [Real.enorm_eq_ofReal (le_of_lt (Real.exp_pos _))]
  exact ⟨h_aesm, h_eLpNorm_lt⟩

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
              (fun ω : FieldConfiguration => ∏ i ∈ s, Real.exp |ω (g i)|) := by
    ext ω; exact Real.exp_sum s (fun i => |ω (g i)|)
  rw [h_eq]
  -- Handle empty case
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp [memLp_const]
  -- For nonempty s, use MemLp.prod' with p i = 2 * s.card for each i
  let k : ℕ := s.card
  have hk_pos : 0 < k := Finset.card_pos.mpr hs
  -- Each factor is in L^(2k)
  have h_each : ∀ i ∈ s, MemLp (fun ω : FieldConfiguration => Real.exp |ω (g i)|)
      (2 * k : ℕ) (muGFF m).toMeasure := by
    intro i _
    exact gff_exp_abs_pairing_memLp m (g i) (2 * k : ℕ) (ENNReal.natCast_ne_top _)
  -- Apply MemLp.prod' with constant exponent 2k for each factor
  have h_prod := MemLp.prod' (s := s) (p := fun _ => (2 * k : ℕ))
    (f := fun i (ω : FieldConfiguration) => Real.exp |ω (g i)|)
    (fun i hi => h_each i hi)
  -- The resulting exponent is (∑ i ∈ s, 1/(2k))⁻¹ = (k/(2k))⁻¹ = 2
  convert h_prod using 1
  -- Goal: 2 = (∑ i ∈ s, ((2 * k : ℕ) : ENNReal)⁻¹)⁻¹
  rw [Finset.sum_const, nsmul_eq_mul]
  -- Goal: 2 = (s.card * ((2 * k : ℕ) : ENNReal)⁻¹)⁻¹
  -- Since k = s.card, this is (k * (2k)⁻¹)⁻¹ = (1/2)⁻¹ = 2
  have hk_ne_zero : (s.card : ENNReal) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    exact hk_pos.ne'
  have hk_ne_top : (s.card : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top s.card
  -- Rewrite (2 * k : ℕ) as 2 * s.card in ENNReal using k = s.card
  simp only [k]
  have h_cast : ((2 * s.card : ℕ) : ENNReal) = 2 * s.card := by norm_cast
  rw [h_cast]
  -- Goal: 2 = (s.card * (2 * s.card)⁻¹)⁻¹
  -- Strategy: s.card * (2 * s.card)⁻¹ = s.card / (2 * s.card) = 1/2, so inverse is 2
  have h2_ne_zero : (2 : ENNReal) ≠ 0 := by norm_num
  have h2_ne_top : (2 : ENNReal) ≠ ⊤ := by norm_num
  -- First simplify (2 * s.card)⁻¹ = 2⁻¹ * s.card⁻¹
  rw [ENNReal.mul_inv (Or.inl h2_ne_zero) (Or.inl h2_ne_top)]
  -- Goal: 2 = (s.card * (2⁻¹ * s.card⁻¹))⁻¹
  rw [mul_comm (2 : ENNReal)⁻¹ (s.card : ENNReal)⁻¹]
  rw [← mul_assoc]
  rw [ENNReal.mul_inv_cancel hk_ne_zero hk_ne_top]
  -- Goal: 2 = (1 * 2⁻¹)⁻¹
  rw [one_mul]
  -- Goal: 2 = 2⁻¹⁻¹
  simp only [inv_inv]

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
      (muGFF m).toMeasure := by
  -- The norm is exp(-(ω f_im)) which is integrable
  have h_norm := gff_integrand_norm_integrable m (∑ i, z i • J i)
  -- Use Integrable.of_norm - h_norm is already an Integrable statement
  -- We need to convert from norm integrable to integrable
  have h_meas : AEStronglyMeasurable
      (fun ω => Complex.exp (Complex.I * distributionPairingℂReal ω (∑ i, z i • J i)))
      (muGFF m).toMeasure := gff_integrand_measurable m n J z
  exact (integrable_norm_iff h_meas).mp h_norm

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
  have h_re_formula : ∀ ω t, (a ω + t * b ω).re = -t.im * ω f_im := by
    intro ω t
    simp only [a, b]
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
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
  -- Young's inequality helper: c|x| ≤ c²/(4α) + αx²
  have young : ∀ (c : ℝ) (α : ℝ), 0 < α → ∀ x : ℝ,
      c * |x| ≤ c ^ 2 / (4 * α) + α * x ^ 2 := by
    intro c α hα x
    have h4α_pos : (0 : ℝ) < 4 * α := by positivity
    rw [show c ^ 2 / (4 * α) + α * x ^ 2
        = (c ^ 2 + 4 * α ^ 2 * x ^ 2) / (4 * α) from by field_simp]
    rw [le_div_iff₀ h4α_pos]
    nlinarith [sq_nonneg (c - 2 * α * |x|), sq_abs x]
  -- Fernique domination: exp(c|ω f_im|) is integrable for any c ≥ 0
  have fernique_dom : ∀ (c : ℝ), 0 ≤ c →
      Integrable (fun ω => Real.exp (c * |ω f_im|)) (muGFF m).toMeasure := by
    intro c _
    obtain ⟨α, hα_pos, h_fernique⟩ := gaussianFreeField_pairing_expSq_integrable m f_im
    have h_dom : Integrable (fun ω => Real.exp (c ^ 2 / (4 * α) + α * (ω f_im) ^ 2))
        (muGFF m).toMeasure := by
      have h := h_fernique.const_mul (Real.exp (c ^ 2 / (4 * α)))
      simp only [distributionPairingCLM_apply, distributionPairing, ← Real.exp_add] at h
      exact h
    apply h_dom.mono
      (Real.continuous_exp.measurable.comp
        (measurable_const.mul (continuous_abs.measurable.comp h_eval_meas_im))
        |>.aestronglyMeasurable)
    filter_upwards with ω
    simp only [Real.norm_eq_abs, Function.comp_def, abs_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_exp.mpr (young c α hα_pos (ω f_im))
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
    apply Real.exp_le_exp.mpr
    calc -t₀.im * ω f_im ≤ |t₀.im * ω f_im| := by
            rw [neg_mul]; exact neg_le.mp (neg_abs_le _)
      _ = |t₀.im| * |ω f_im| := abs_mul _ _
      _ ≤ _ := le_refl _
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
          apply Real.exp_le_exp.mpr
          calc -t.im * ω f_im ≤ |t.im * ω f_im| := by
                  rw [neg_mul]; exact neg_le.mp (neg_abs_le _)
            _ = |t.im| * |ω f_im| := abs_mul _ _
            _ ≤ (|t₀.im| + 1) * |ω f_im| := by
                apply mul_le_mul_of_nonneg_right (h_im_bound t ht) (abs_nonneg _)
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
    apply AnalyticOnNhd.add
    · apply AnalyticOnNhd.add
      · exact analyticOnNhd_const
      · -- 2 * t * Q_ri is linear in t
        have : AnalyticOnNhd ℂ (fun t : ℂ =>
            (2 * (freeCovarianceFormR m f_re f_im : ℂ)) * t) Set.univ :=
          AnalyticOnNhd.mul analyticOnNhd_const analyticOnNhd_id
        convert this using 2; ring
    · -- t^2 * Q_ii is polynomial in t
      apply AnalyticOnNhd.mul _ analyticOnNhd_const
      exact (analyticOnNhd_id (𝕜 := ℂ)).pow 2
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
  have h := freeCovarianceℂ_bilinear_smul_right m (0 : ℂ) f (0 : TestFunctionℂ)
  simpa only [zero_smul, zero_mul] using h

/-- C_ℂ(0, g) = 0, derived from smul_left with c = 0. -/
private lemma freeCovarianceℂ_bilinear_zero_left (g : TestFunctionℂ) :
    freeCovarianceℂBilinear m 0 g = 0 := by
  have h := freeCovarianceℂ_bilinear_smul_left m (0 : ℂ) (0 : TestFunctionℂ) g
  simpa only [zero_smul, zero_mul] using h

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
