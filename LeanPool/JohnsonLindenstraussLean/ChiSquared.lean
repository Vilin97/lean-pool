import JL.SquaredGaussian

/-!
# Chi-squared moment generating function and concentration

Building on `sqGaussian_mgf`, this file constructs the sum of `k` i.i.d. squared
standard Gaussians as the coordinate sum under the product measure
`gaussianVec k = Measure.pi (fun _ : Fin k => stdGaussian)`, computes its moment
generating function

`mgf (chiSq k) (gaussianVec k) t = ((1 - 2t)^(-1/2))^k`,

and derives two-sided **chi-squared tail bounds** via mathlib's Chernoff bound,
optimised at the Dasgupta–Gupta choice of `t`:

* upper: `P(S ≥ (1+ε)k) ≤ exp(-(ε² - ε³) k / 4)`,
* lower: `P(S ≤ (1-ε)k) ≤ exp(-(ε² - ε³) k / 4)`.

The analytic crux is reduced to two scalar logarithmic inequalities, proven by
the monotonicity of an explicit auxiliary function.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace JL

/-! ## Scalar logarithmic inequalities -/

/-- `log (1 + ε) ≤ ε - ε²/2 + ε³/2` for `ε ≥ 0`. -/
lemma log_one_add_le {ε : ℝ} (hε : 0 ≤ ε) :
    Real.log (1 + ε) ≤ ε - ε ^ 2 / 2 + ε ^ 3 / 2 := by
  have hderiv : ∀ x : ℝ, -1 < x →
      HasDerivAt (fun y : ℝ => y - y ^ 2 / 2 + y ^ 3 / 2 - Real.log (1 + y))
        (1 - x + 3 / 2 * x ^ 2 - 1 / (1 + x)) x := by
    intro x hx
    have hx0 : (1 : ℝ) + x ≠ 0 := by linarith
    have hlog : HasDerivAt (fun y : ℝ => Real.log (1 + y)) (1 / (1 + x)) x := by
      simpa using ((hasDerivAt_id x).const_add (1 : ℝ)).log hx0
    have hcomb := (((hasDerivAt_id' (x := x)).sub ((hasDerivAt_pow 2 x).div_const 2)).add
      ((hasDerivAt_pow 3 x).div_const 2)).sub hlog
    exact hcomb.congr_deriv (by push_cast; ring)
  have hcont : ContinuousOn (fun y : ℝ => y - y ^ 2 / 2 + y ^ 3 / 2 - Real.log (1 + y))
      (Set.Ici 0) := fun x hx =>
    (hderiv x (by simp only [Set.mem_Ici] at hx; linarith)).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun y : ℝ => y - y ^ 2 / 2 + y ^ 3 / 2 - Real.log (1 + y))
      (interior (Set.Ici 0)) := by
    rw [interior_Ici]
    exact fun x hx =>
      (hderiv x (by simp only [Set.mem_Ioi] at hx; linarith)).differentiableAt.differentiableWithinAt
  have hmono : MonotoneOn (fun y : ℝ => y - y ^ 2 / 2 + y ^ 3 / 2 - Real.log (1 + y))
      (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hcont hdiff
    rw [interior_Ici]
    intro x hx
    simp only [Set.mem_Ioi] at hx
    rw [(hderiv x (by linarith)).deriv]
    have hb : (0 : ℝ) < 1 + x := by linarith
    rw [show 1 - x + 3 / 2 * x ^ 2 - 1 / (1 + x)
        = (1 / 2 * x ^ 2 + 3 / 2 * x ^ 3) / (1 + x) by field_simp; ring]
    apply div_nonneg _ hb.le
    have h2 := pow_nonneg hx.le 2
    have h3 := pow_nonneg hx.le 3
    linarith
  have key := hmono Set.self_mem_Ici (Set.mem_Ici.mpr hε) hε
  have lhs0 : (fun y : ℝ => y - y ^ 2 / 2 + y ^ 3 / 2 - Real.log (1 + y)) 0 = 0 := by simp
  have rhsε : (fun y : ℝ => y - y ^ 2 / 2 + y ^ 3 / 2 - Real.log (1 + y)) ε
      = ε - ε ^ 2 / 2 + ε ^ 3 / 2 - Real.log (1 + ε) := rfl
  rw [lhs0, rhsε] at key
  linarith

/-- `log (1 - ε) ≤ -ε - ε²/2 + ε³/2` for `0 ≤ ε < 1`. -/
lemma log_one_sub_le {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1) :
    Real.log (1 - ε) ≤ -ε - ε ^ 2 / 2 + ε ^ 3 / 2 := by
  have hderiv : ∀ x : ℝ, x < 1 →
      HasDerivAt (fun y : ℝ => -y - y ^ 2 / 2 + y ^ 3 / 2 - Real.log (1 - y))
        (-1 - x + 3 / 2 * x ^ 2 + 1 / (1 - x)) x := by
    intro x hx
    have hx0 : (1 : ℝ) - x ≠ 0 := by linarith
    have hlog : HasDerivAt (fun y : ℝ => Real.log (1 - y)) (-1 / (1 - x)) x := by
      simpa using ((hasDerivAt_id x).const_sub (1 : ℝ)).log hx0
    have hcomb := ((((hasDerivAt_id' (x := x)).neg).sub ((hasDerivAt_pow 2 x).div_const 2)).add
      ((hasDerivAt_pow 3 x).div_const 2)).sub hlog
    exact hcomb.congr_deriv (by push_cast; ring)
  have hcont : ContinuousOn (fun y : ℝ => -y - y ^ 2 / 2 + y ^ 3 / 2 - Real.log (1 - y))
      (Set.Ico 0 1) := fun x hx =>
    (hderiv x (Set.mem_Ico.mp hx).2).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun y : ℝ => -y - y ^ 2 / 2 + y ^ 3 / 2 - Real.log (1 - y))
      (interior (Set.Ico 0 1)) := by
    rw [interior_Ico]
    exact fun x hx =>
      (hderiv x (Set.mem_Ioo.mp hx).2).differentiableAt.differentiableWithinAt
  have hmono : MonotoneOn (fun y : ℝ => -y - y ^ 2 / 2 + y ^ 3 / 2 - Real.log (1 - y))
      (Set.Ico 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ico 0 1) hcont hdiff
    rw [interior_Ico]
    intro x hx
    simp only [Set.mem_Ioo] at hx
    rw [(hderiv x hx.2).deriv]
    have hb : (0 : ℝ) < 1 - x := by linarith
    rw [show -1 - x + 3 / 2 * x ^ 2 + 1 / (1 - x)
        = (5 / 2 * x ^ 2 - 3 / 2 * x ^ 3) / (1 - x) by field_simp; ring]
    apply div_nonneg _ hb.le
    nlinarith [mul_nonneg (sq_nonneg x) (show (0 : ℝ) ≤ 5 - 3 * x by linarith), sq_nonneg x]
  have key := hmono (Set.mem_Ico.mpr ⟨le_refl 0, by norm_num⟩) (Set.mem_Ico.mpr ⟨hε, hε1⟩) hε
  have lhs0 : (fun y : ℝ => -y - y ^ 2 / 2 + y ^ 3 / 2 - Real.log (1 - y)) 0 = 0 := by simp
  have rhsε : (fun y : ℝ => -y - y ^ 2 / 2 + y ^ 3 / 2 - Real.log (1 - y)) ε
      = -ε - ε ^ 2 / 2 + ε ^ 3 / 2 - Real.log (1 - ε) := rfl
  rw [lhs0, rhsε] at key
  linarith

/-- The base scalar inequality controlling the upper chi-squared tail. -/
lemma scalar_upper {ε : ℝ} (h0 : 0 < ε) :
    rexp (-(ε / 2)) * √(1 + ε) ≤ rexp (-(ε ^ 2 - ε ^ 3) / 4) := by
  have hb : (0 : ℝ) < 1 + ε := by linarith
  rw [← Real.exp_log (show (0 : ℝ) < rexp (-(ε / 2)) * √(1 + ε) by positivity)]
  apply Real.exp_le_exp.mpr
  rw [Real.log_mul (Real.exp_pos _).ne' (Real.sqrt_ne_zero'.mpr hb), Real.log_exp,
    Real.log_sqrt hb.le]
  have := log_one_add_le h0.le
  linarith

/-- The base scalar inequality controlling the lower chi-squared tail. -/
lemma scalar_lower {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    rexp (ε / 2) * √(1 - ε) ≤ rexp (-(ε ^ 2 - ε ^ 3) / 4) := by
  have hb : (0 : ℝ) < 1 - ε := by linarith
  rw [← Real.exp_log (show (0 : ℝ) < rexp (ε / 2) * √(1 - ε) by positivity)]
  apply Real.exp_le_exp.mpr
  rw [Real.log_mul (Real.exp_pos _).ne' (Real.sqrt_ne_zero'.mpr hb), Real.log_exp,
    Real.log_sqrt hb.le]
  have := log_one_sub_le h0.le h1
  linarith

/-! ## The chi-squared random variable and its MGF -/

/-- The product Gaussian measure on `Fin k → ℝ`: `k` i.i.d. `N(0,1)` coordinates. -/
noncomputable def gaussianVec (k : ℕ) : Measure (Fin k → ℝ) :=
  Measure.pi (fun _ => stdGaussian)

instance (k : ℕ) : IsProbabilityMeasure (gaussianVec k) := by
  unfold gaussianVec; infer_instance

/-- The chi-squared random variable with `k` degrees of freedom: the sum of the
squared coordinates. -/
noncomputable def chiSq (k : ℕ) : (Fin k → ℝ) → ℝ := fun ω => ∑ i, (ω i) ^ 2

/-- **Chi-squared MGF.** For `t < 1/2`, `E[exp (t · S)] = ((1 - 2t)^(-1/2))^k`. -/
theorem chiSq_mgf (k : ℕ) {t : ℝ} (ht : t < 1 / 2) :
    mgf (chiSq k) (gaussianVec k) t = ((√(1 - 2 * t))⁻¹) ^ k := by
  have hpi : gaussianVec k = Measure.pi (fun _ : Fin k => stdGaussian) := rfl
  have hsum : chiSq k = ∑ i, (fun ω : Fin k → ℝ => (ω i) ^ 2) := by
    funext ω; simp [chiSq, Finset.sum_apply]
  have hmeas : ∀ i : Fin k, Measurable (fun ω : Fin k → ℝ => (ω i) ^ 2) := fun i => by fun_prop
  have hlaw : ∀ i : Fin k, (gaussianVec k).map (fun ω => (ω i) ^ 2)
      = stdGaussian.map (fun x : ℝ => x ^ 2) := by
    intro i
    have hev : (gaussianVec k).map (fun a : Fin k → ℝ => a i) = stdGaussian := by
      have h := (measurePreserving_eval (μ := fun _ : Fin k => stdGaussian) i).map_eq
      rw [hpi]; simpa [Function.eval] using h
    calc (gaussianVec k).map (fun ω => (ω i) ^ 2)
        = (gaussianVec k).map ((fun x : ℝ => x ^ 2) ∘ (fun a => a i)) := rfl
      _ = ((gaussianVec k).map (fun a => a i)).map (fun x : ℝ => x ^ 2) :=
          (Measure.map_map (g := fun x : ℝ => x ^ 2) (by fun_prop) (measurable_pi_apply i)).symm
      _ = stdGaussian.map (fun x : ℝ => x ^ 2) := by rw [hev]
  have hmgf_single : ∀ i : Fin k,
      mgf (fun ω => (ω i) ^ 2) (gaussianVec k) t = (√(1 - 2 * t))⁻¹ := by
    intro i
    have hAE : AEMeasurable (fun ω : Fin k → ℝ => (ω i) ^ 2) (gaussianVec k) :=
      (hmeas i).aemeasurable
    have hAE2 : AEMeasurable (fun x : ℝ => x ^ 2) stdGaussian := by fun_prop
    rw [← mgf_id_map hAE, hlaw i, mgf_id_map hAE2, sqGaussian_mgf ht]
  have hindep : iIndepFun (fun (i : Fin k) (ω : Fin k → ℝ) => (ω i) ^ 2) (gaussianVec k) :=
    iIndepFun_pi (fun _ => (by fun_prop : AEMeasurable (fun x : ℝ => x ^ 2) stdGaussian))
  have hident : ∀ i : Fin k, ∀ j : Fin k,
      IdentDistrib (fun ω => (ω i) ^ 2) (fun ω => (ω j) ^ 2) (gaussianVec k) (gaussianVec k) := by
    intro i j
    exact ⟨(hmeas i).aemeasurable, (hmeas j).aemeasurable, by rw [hlaw i, hlaw j]⟩
  rw [hsum]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · rw [mgf_sum_of_identDistrib hmeas hindep (fun i _ j _ => hident i j)
      (Finset.mem_univ (⟨0, hk⟩ : Fin k)) t, hmgf_single, Finset.card_univ, Fintype.card_fin]

/-- Integrability of `exp (t · Z²)` against `N(0,1)` for `t < 1/2`. -/
lemma integrable_exp_mul_sq {t : ℝ} (ht : t < 1 / 2) :
    Integrable (fun x : ℝ => rexp (t * x ^ 2)) stdGaussian := by
  have hb : (0 : ℝ) < 1 / 2 - t := by linarith
  rw [stdGaussian, gaussianReal_of_var_ne_zero _ (show (1 : ℝ≥0) ≠ 0 by norm_num),
    integrable_withDensity_iff_integrable_smul₀' (by fun_prop)
      (ae_of_all _ (fun _ => gaussianPDF_lt_top))]
  have heq : (fun x : ℝ => (gaussianPDF 0 1 x).toReal • rexp (t * x ^ 2))
      = (fun x : ℝ => (√(2 * π))⁻¹ * rexp (-(1 / 2 - t) * x ^ 2)) := by
    funext x
    rw [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _), smul_eq_mul,
      stdGaussian_pdf, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [heq]
  exact (integrable_exp_neg_mul_sq hb).const_mul _

/-- Integrability of `exp (t · S)` for `t < 1/2`. -/
theorem integrable_exp_mul_chiSq (k : ℕ) {t : ℝ} (ht : t < 1 / 2) :
    Integrable (fun ω => rexp (t * chiSq k ω)) (gaussianVec k) := by
  have hfac : (fun ω => rexp (t * chiSq k ω))
      = (fun ω : Fin k → ℝ => ∏ i, rexp (t * (ω i) ^ 2)) := by
    funext ω
    rw [chiSq, Finset.mul_sum, Real.exp_sum]
  rw [hfac]
  exact Integrable.fintype_prod (f := fun _ x => rexp (t * x ^ 2))
    (fun _ => integrable_exp_mul_sq ht)

/-! ## Two-sided chi-squared tail bounds -/

/-- **Upper chi-squared tail.** `P(S ≥ (1+ε)k) ≤ exp(-(ε² - ε³) k / 4)`. -/
theorem chiSq_upper_tail (k : ℕ) {ε : ℝ} (h0 : 0 < ε) :
    (gaussianVec k).real {ω | (1 + ε) * (k : ℝ) ≤ chiSq k ω}
      ≤ rexp (-(ε ^ 2 - ε ^ 3) * (k : ℝ) / 4) := by
  have hε1 : (0 : ℝ) < 1 + ε := by linarith
  set t : ℝ := ε / (2 * (1 + ε)) with ht_def
  have ht0 : 0 ≤ t := by rw [ht_def]; exact div_nonneg h0.le (by linarith)
  have ht_half : t < 1 / 2 := by
    rw [ht_def, div_lt_iff₀ (by linarith : (0 : ℝ) < 2 * (1 + ε))]; linarith
  have hmgf_eq : (√(1 - 2 * t))⁻¹ = √(1 + ε) := by
    rw [show (1 : ℝ) - 2 * t = (1 + ε)⁻¹ by rw [ht_def]; field_simp; ring,
      Real.sqrt_inv, inv_inv]
  have hcher := measure_ge_le_exp_mul_mgf (X := chiSq k) (μ := gaussianVec k)
    ((1 + ε) * (k : ℝ)) ht0 (integrable_exp_mul_chiSq k ht_half)
  rw [chiSq_mgf k ht_half, hmgf_eq] at hcher
  refine hcher.trans ?_
  have hexp1 : -t * ((1 + ε) * (k : ℝ)) = (k : ℝ) * (-(ε / 2)) := by
    rw [ht_def]; field_simp
  have hexp2 : -(ε ^ 2 - ε ^ 3) * (k : ℝ) / 4 = (k : ℝ) * (-(ε ^ 2 - ε ^ 3) / 4) := by ring
  rw [hexp1, hexp2, Real.exp_nat_mul, Real.exp_nat_mul, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) (scalar_upper h0) k

/-- **Lower chi-squared tail.** `P(S ≤ (1-ε)k) ≤ exp(-(ε² - ε³) k / 4)`. -/
theorem chiSq_lower_tail (k : ℕ) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    (gaussianVec k).real {ω | chiSq k ω ≤ (1 - ε) * (k : ℝ)}
      ≤ rexp (-(ε ^ 2 - ε ^ 3) * (k : ℝ) / 4) := by
  have hε1 : (0 : ℝ) < 1 - ε := by linarith
  set t : ℝ := -(ε / (2 * (1 - ε))) with ht_def
  have ht_neg : t ≤ 0 := by
    rw [ht_def, neg_nonpos]; exact div_nonneg h0.le (by linarith)
  have ht_half : t < 1 / 2 := lt_of_le_of_lt ht_neg (by norm_num)
  have hmgf_eq : (√(1 - 2 * t))⁻¹ = √(1 - ε) := by
    rw [show (1 : ℝ) - 2 * t = (1 - ε)⁻¹ by rw [ht_def]; field_simp; ring,
      Real.sqrt_inv, inv_inv]
  have hcher := measure_le_le_exp_mul_mgf (X := chiSq k) (μ := gaussianVec k)
    ((1 - ε) * (k : ℝ)) ht_neg (integrable_exp_mul_chiSq k ht_half)
  rw [chiSq_mgf k ht_half, hmgf_eq] at hcher
  refine hcher.trans ?_
  have hexp1 : -t * ((1 - ε) * (k : ℝ)) = (k : ℝ) * (ε / 2) := by
    rw [ht_def]; field_simp
  have hexp2 : -(ε ^ 2 - ε ^ 3) * (k : ℝ) / 4 = (k : ℝ) * (-(ε ^ 2 - ε ^ 3) / 4) := by ring
  rw [hexp1, hexp2, Real.exp_nat_mul, Real.exp_nat_mul, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) (scalar_lower h0 h1) k

end JL
