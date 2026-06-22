/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.GeneralizedResidueTheory.Homotopy.Integrality

/-!
# Circle Parameterizations

Standard circle parameterizations (counterclockwise and clockwise) and
their winding number computations.

## Main Results

* `circleParam` — counterclockwise circle: `z₀ + r·exp(2πi(t-a)/(b-a))`
* `circleParam_winding_eq_one` — winding number = 1
* `circleParamCW` — clockwise circle: reversal of `circleParam`
* `circleParamCW_winding_eq_neg_one` — winding number = -1
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

private noncomputable instance : ContinuousSMul ℝ ℂ :=
  ⟨(show (fun p : ℝ × ℂ => p.1 • p.2) = (fun p => (p.1 : ℂ) * p.2) from
    funext fun p => by simp [Complex.real_smul]) ▸
    (Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd⟩

/-- Standard circle parameterization: `z₀ + r·exp(2πi(t-a)/(b-a))`. -/
def circleParam (z₀ : ℂ) (r : ℝ) (a b : ℝ) (t : ℝ) : ℂ :=
  z₀ + r * exp (2 * Real.pi * I * ((t - a) / (b - a)))

lemma circleParam_continuous (z₀ : ℂ) (r : ℝ) (a b : ℝ) :
    Continuous (circleParam z₀ r a b) := by
  unfold circleParam
  exact Continuous.add continuous_const (Continuous.mul continuous_const
    (Complex.continuous_exp.comp (Continuous.mul continuous_const
    ((continuous_ofReal.sub continuous_const).div_const _))))

lemma circleParam_closed (z₀ : ℂ) (r : ℝ) (a b : ℝ) (hab : a < b) :
    circleParam z₀ r a b a = circleParam z₀ r a b b := by
  simp only [circleParam]
  have hne : (b : ℂ) - a ≠ 0 := by
    simp only [sub_ne_zero, Complex.ofReal_inj, ne_eq]; exact ne_of_gt hab
  have ha : ((a : ℂ) - a) / ((b : ℂ) - a) = 0 := by simp only [sub_self, zero_div]
  have hb : ((b : ℂ) - a) / ((b : ℂ) - a) = 1 := div_self hne
  simp only [ha, hb, mul_zero, exp_zero, mul_one, exp_two_pi_mul_I]

lemma circleParam_dist (z₀ : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (a b : ℝ) (_hab : a < b) (t : ℝ) :
    ‖circleParam z₀ r a b t - z₀‖ = r := by
  simp only [circleParam, add_sub_cancel_left, norm_mul, Complex.norm_real,
    Complex.norm_exp, mul_re, ofReal_re, ofReal_im, I_re, I_im]
  ring_nf
  simp [Real.exp_zero, abs_of_nonneg hr]

lemma circleParam_deriv (z₀ : ℂ) (r : ℝ) (a b : ℝ)
    (_hab : a < b) (t : ℝ) :
    deriv (circleParam z₀ r a b) t =
    r * (2 * Real.pi * I / (b - a)) *
      exp (2 * Real.pi * I * ((t - a) / (b - a))) := by
  unfold circleParam
  let f : ℝ → ℂ := fun t =>
    2 * Real.pi * I * (((t : ℂ) - a) / (b - a))
  have hf_deriv : HasDerivAt f (2 * Real.pi * I / (b - a)) t := by
    have h_eq : f = fun t : ℝ =>
        (2 * Real.pi * I / (b - a)) * ((t : ℂ) - a) := by
      ext t; simp only [f]; field_simp
    rw [h_eq]
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) - (a : ℂ)) 1 t :=
      Complex.ofRealCLM.hasDerivAt.sub_const (a : ℂ)
    simpa using h1.const_mul (2 * Real.pi * I / (b - a))
  have hexp_comp : HasDerivAt (fun t => exp (f t))
      (exp (f t) * (2 * Real.pi * I / (b - a))) t :=
    hf_deriv.cexp
  have hmul : HasDerivAt (fun t => (r : ℂ) * exp (f t))
      ((r : ℂ) * (exp (f t) *
        (2 * Real.pi * I / (b - a)))) t :=
    hexp_comp.const_mul (r : ℂ)
  have hadd : HasDerivAt
      (fun t => z₀ + (r : ℂ) * exp (f t))
      (0 + (r : ℂ) * (exp (f t) *
        (2 * Real.pi * I / (b - a)))) t :=
    (hasDerivAt_const t z₀).add hmul
  simp only [zero_add] at hadd
  rw [hadd.deriv]; ring

lemma circleParam_integrand_const (z₀ : ℂ) (r : ℝ)
    (hr : 0 < r) (a b : ℝ) (hab : a < b) (t : ℝ) :
    (circleParam z₀ r a b t - z₀)⁻¹ *
      deriv (circleParam z₀ r a b) t =
    2 * Real.pi * I / (b - a) := by
  rw [circleParam_deriv z₀ r a b hab t]
  simp only [circleParam, add_sub_cancel_left]
  field_simp [Complex.ofReal_ne_zero.mpr (ne_of_gt hr),
    exp_ne_zero _]

/-- The winding number of a CCW circle around its center is 1. -/
theorem circleParam_winding_eq_one (z₀ : ℂ) (r : ℝ)
    (hr : 0 < r) (a b : ℝ) (hab : a < b) :
    generalizedWindingNumber' (circleParam z₀ r a b) a b z₀ =
      1 := by
  have havoids : ∀ t, ‖circleParam z₀ r a b t - z₀‖ = r :=
    fun t => circleParam_dist z₀ r (hr.le) a b hab t
  unfold generalizedWindingNumber' cauchyPrincipalValue'
  have hint_const : ∀ ε > 0, ε < r →
      (∫ t in a..b,
        if ‖circleParam z₀ r a b t - z₀‖ > ε then
          (circleParam z₀ r a b t - z₀)⁻¹ *
            deriv (circleParam z₀ r a b) t
        else 0) =
      2 * Real.pi * I := by
    intro ε _hε_pos hε_lt_r
    have h_cond : ∀ t,
        ‖circleParam z₀ r a b t - z₀‖ > ε := fun t => by
      rw [havoids]; exact hε_lt_r
    have h_simp :
        (fun t => if ‖circleParam z₀ r a b t - z₀‖ > ε
          then (circleParam z₀ r a b t - z₀)⁻¹ *
            deriv (circleParam z₀ r a b) t
          else 0) =
        fun _ => 2 * Real.pi * I / (b - a) := by
      ext t; simp only [h_cond t, ↓reduceIte]
      exact circleParam_integrand_const z₀ r hr a b hab t
    rw [h_simp, intervalIntegral.integral_const]
    have hba_ne : (b : ℂ) - a ≠ 0 := by
      simp only [sub_ne_zero, Complex.ofReal_inj, ne_eq]
      exact ne_of_gt hab
    erw [Complex.real_smul]; rw [Complex.ofReal_sub]
    field_simp
  have hlim : Tendsto (fun ε => ∫ t in a..b,
        if ‖circleParam z₀ r a b t - z₀‖ > ε then
          (circleParam z₀ r a b t - z₀)⁻¹ *
            deriv (circleParam z₀ r a b) t
        else 0) (𝓝[>] (0 : ℝ)) (𝓝 (2 * Real.pi * I)) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [Ioo_mem_nhdsGT hr] with ε hε
      exact (hint_const ε (mem_Ioo.mp hε).1 (mem_Ioo.mp hε).2).symm)
  have h_match :
      (fun ε => ∫ t in a..b,
        if ‖(fun t => circleParam z₀ r a b t - z₀) t - 0‖ >
          ε
        then
          (fun x => x⁻¹)
            ((fun t => circleParam z₀ r a b t - z₀) t) *
            deriv (fun t =>
              circleParam z₀ r a b t - z₀) t
        else 0) =
      (fun ε => ∫ t in a..b,
        if ‖circleParam z₀ r a b t - z₀‖ > ε then
          (circleParam z₀ r a b t - z₀)⁻¹ *
            deriv (circleParam z₀ r a b) t
        else 0) := by
    ext ε; congr 1 with t
    simp only [sub_zero, deriv_sub_const]
  simp only [h_match, hlim.limUnder_eq]
  have hpi_ne : (2 : ℂ) * Real.pi * I ≠ 0 := by
    simp [ne_eq, mul_eq_zero, Complex.ofReal_eq_zero,
      Real.pi_ne_zero, I_ne_zero]
  field_simp

/-- Clockwise circle parameterization: reversal of `circleParam`.
`circleParamCW z₀ r a b t = circleParam z₀ r a b (a + b - t)` -/
def circleParamCW (z₀ : ℂ) (r : ℝ) (a b : ℝ) (t : ℝ) : ℂ :=
  circleParam z₀ r a b (a + b - t)

lemma circleParamCW_continuous (z₀ : ℂ) (r : ℝ) (a b : ℝ) :
    Continuous (circleParamCW z₀ r a b) := by
  unfold circleParamCW
  exact (circleParam_continuous z₀ r a b).comp
    (continuous_const.sub continuous_id)

lemma circleParamCW_closed (z₀ : ℂ) (r : ℝ) (a b : ℝ)
    (hab : a < b) :
    circleParamCW z₀ r a b a =
      circleParamCW z₀ r a b b := by
  simp only [circleParamCW]
  have ha : a + b - a = b := by ring
  have hb : a + b - b = a := by ring
  rw [ha, hb]
  exact (circleParam_closed z₀ r a b hab).symm

lemma circleParamCW_dist (z₀ : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (a b : ℝ) (hab : a < b) (t : ℝ) :
    ‖circleParamCW z₀ r a b t - z₀‖ = r := by
  simp only [circleParamCW]
  exact circleParam_dist z₀ r hr a b hab (a + b - t)

lemma circleParam_differentiable (z₀ : ℂ) (r : ℝ)
    (a b : ℝ) :
    Differentiable ℝ (circleParam z₀ r a b) := by
  unfold circleParam
  apply Differentiable.add
  · exact differentiable_const z₀
  · apply Differentiable.mul
    · exact differentiable_const _
    · apply Differentiable.cexp
      apply Differentiable.mul
      · exact differentiable_const _
      · apply Differentiable.div_const
        apply Differentiable.sub
        · exact Complex.ofRealCLM.differentiable.comp
            differentiable_id
        · exact differentiable_const _

lemma circleParamCW_differentiable (z₀ : ℂ) (r : ℝ)
    (a b : ℝ) :
    Differentiable ℝ (circleParamCW z₀ r a b) := by
  unfold circleParamCW
  exact (circleParam_differentiable z₀ r a b).comp
    ((differentiable_const _).sub differentiable_id)

lemma circleParamCW_hasDerivAt (z₀ : ℂ) (r : ℝ)
    (a b : ℝ) (hab : a < b) (t : ℝ) :
    HasDerivAt (circleParamCW z₀ r a b)
      (-(r * (2 * Real.pi * I / (b - a)) *
        exp (2 * Real.pi * I *
          (((a + b - t : ℝ) - a) / (b - a))))) t := by
  unfold circleParamCW
  have hdiff :
      DifferentiableAt ℝ (circleParam z₀ r a b)
        (a + b - t) :=
    (circleParam_differentiable z₀ r a b).differentiableAt
  have hg : HasDerivAt
      (fun t : ℝ => (a + b - t : ℝ)) (-1 : ℝ) t := by
    simpa using (hasDerivAt_id t).const_sub (a + b)
  have hf : HasDerivAt (circleParam z₀ r a b)
      (r * (2 * Real.pi * I / (b - a)) *
        exp (2 * Real.pi * I *
          ((↑(a + b - t) - a) / (b - a))))
      (a + b - t) := by
    have hd :=
      circleParam_deriv z₀ r a b hab (a + b - t)
    rw [← hd]
    exact hdiff.hasDerivAt
  have hchain := HasDerivAt.scomp t hf hg
  simp only [neg_one_smul] at hchain
  exact hchain

lemma circleParamCW_deriv (z₀ : ℂ) (r : ℝ) (a b : ℝ)
    (hab : a < b) (t : ℝ) :
    deriv (circleParamCW z₀ r a b) t =
    -(r * (2 * Real.pi * I / (b - a)) *
      exp (2 * Real.pi * I *
        (((a + b - t : ℝ) - a) / (b - a)))) :=
  (circleParamCW_hasDerivAt z₀ r a b hab t).deriv

lemma circleParamCW_integrand_neg (z₀ : ℂ) (r : ℝ)
    (hr : 0 < r) (a b : ℝ) (hab : a < b) (t : ℝ) :
    (circleParamCW z₀ r a b t - z₀)⁻¹ *
      deriv (circleParamCW z₀ r a b) t =
    -(2 * Real.pi * I / (b - a)) := by
  rw [circleParamCW_deriv z₀ r a b hab t]
  simp only [circleParamCW, circleParam,
    add_sub_cancel_left]
  have hr_ne : (r : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  have hexp_ne :
      exp (2 * Real.pi * I *
        (((a + b - t : ℝ) - a) / (b - a))) ≠ 0 :=
    exp_ne_zero _
  field_simp [hr_ne, hexp_ne]

/-- Winding number of a CW circle around its center is -1. -/
theorem circleParamCW_winding_eq_neg_one (z₀ : ℂ)
    (r : ℝ) (hr : 0 < r) (a b : ℝ) (hab : a < b) :
    generalizedWindingNumber' (circleParamCW z₀ r a b)
      a b z₀ = -1 := by
  have havoids :
      ∀ t, ‖circleParamCW z₀ r a b t - z₀‖ = r :=
    fun t =>
      circleParamCW_dist z₀ r (hr.le) a b hab t
  unfold generalizedWindingNumber' cauchyPrincipalValue'
  have hint_const : ∀ ε > 0, ε < r →
      (∫ t in a..b,
        if ‖circleParamCW z₀ r a b t - z₀‖ > ε then
          (circleParamCW z₀ r a b t - z₀)⁻¹ *
            deriv (circleParamCW z₀ r a b) t
        else 0) =
      -2 * Real.pi * I := by
    intro ε _hε_pos hε_lt_r
    have h_cond : ∀ t,
        ‖circleParamCW z₀ r a b t - z₀‖ > ε :=
      fun t => by rw [havoids]; exact hε_lt_r
    have h_simp :
        (fun t =>
          if ‖circleParamCW z₀ r a b t - z₀‖ > ε
          then (circleParamCW z₀ r a b t - z₀)⁻¹ *
            deriv (circleParamCW z₀ r a b) t
          else 0) =
        fun _ => -(2 * Real.pi * I / (b - a)) := by
      ext t; simp only [h_cond t, ↓reduceIte]
      exact circleParamCW_integrand_neg z₀ r hr a b hab t
    rw [h_simp, intervalIntegral.integral_const]
    have hba_ne : (b : ℂ) - a ≠ 0 := by
      simp only [sub_ne_zero, Complex.ofReal_inj, ne_eq]
      exact ne_of_gt hab
    erw [Complex.real_smul]; rw [Complex.ofReal_sub]
    field_simp [hba_ne]
  have hlim : Tendsto (fun ε => ∫ t in a..b,
        if ‖circleParamCW z₀ r a b t - z₀‖ > ε then
          (circleParamCW z₀ r a b t - z₀)⁻¹ *
            deriv (circleParamCW z₀ r a b) t
        else 0) (𝓝[>] (0 : ℝ)) (𝓝 (-2 * Real.pi * I)) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [Ioo_mem_nhdsGT hr] with ε hε
      exact (hint_const ε (mem_Ioo.mp hε).1 (mem_Ioo.mp hε).2).symm)
  have h_match :
      (fun ε => ∫ t in a..b,
        if ‖(fun t =>
            circleParamCW z₀ r a b t - z₀) t - 0‖ > ε
        then
          (fun x => x⁻¹)
            ((fun t =>
              circleParamCW z₀ r a b t - z₀) t) *
            deriv (fun t =>
              circleParamCW z₀ r a b t - z₀) t
        else 0) =
      (fun ε => ∫ t in a..b,
        if ‖circleParamCW z₀ r a b t - z₀‖ > ε then
          (circleParamCW z₀ r a b t - z₀)⁻¹ *
            deriv (circleParamCW z₀ r a b) t
        else 0) := by
    ext ε; congr 1 with t
    simp only [sub_zero, deriv_sub_const]
  simp only [h_match, hlim.limUnder_eq]
  have hpi_ne : (2 : ℂ) * Real.pi * I ≠ 0 := by
    simp [ne_eq, mul_eq_zero, Complex.ofReal_eq_zero,
      Real.pi_ne_zero, I_ne_zero]
  field_simp [hpi_ne]

private lemma hasDerivAt_ofReal_comp (θ : ℝ → ℝ) (t : ℝ)
    (hθ : DifferentiableAt ℝ θ t) :
    HasDerivAt (fun u => (θ u : ℂ)) (Complex.ofReal (deriv θ t)) t := by
  simpa using (hθ.hasDerivAt).ofReal_comp (z := t)

/-- For a C¹ curve on S¹ with angle lift θ, the winding number equals the degree. -/
theorem winding_of_S1_curve_eq_degree (z₀ : ℂ) (a b : ℝ) (_hab : a < b)
    (n : ℤ) (θ : ℝ → ℝ) (hθ_diff : Differentiable ℝ θ)
    (hθ_deriv_cont : Continuous (deriv θ))
    (hθ_change : θ b - θ a = 2 * Real.pi * n) :
    let γ := fun t => z₀ + exp (I * (θ t : ℂ))
    generalizedWindingNumber' γ a b z₀ = n := by
  intro γ
  have hγ_deriv : ∀ t, HasDerivAt γ
      (I * (Complex.ofReal (deriv θ t)) *
        exp (I * (θ t : ℂ))) t := by
    intro t
    have h1 := hasDerivAt_ofReal_comp θ t (hθ_diff t)
    have h2 := h1.const_mul I
    have h3 : HasDerivAt (fun u => exp (I * (θ u : ℂ)))
        (exp (I * (θ t : ℂ)) * (I * (Complex.ofReal (deriv θ t)))) t :=
      ((hasDerivAt_exp _).scomp t h2).congr_deriv (by rw [smul_eq_mul]; ring)
    have h4 := (hasDerivAt_const t z₀).add h3
    simp only [zero_add] at h4
    exact h4.congr_deriv (by ring)
  have h_integrand : ∀ t,
      (γ t - z₀)⁻¹ * deriv γ t =
      I * (Complex.ofReal (deriv θ t)) := by
    intro t
    have hderiv : deriv γ t = I * (Complex.ofReal (deriv θ t)) * exp (I * (θ t : ℂ)) :=
      (hγ_deriv t).deriv
    simp only [γ, add_sub_cancel_left, hderiv]
    field_simp [exp_ne_zero]
  have h_integral : ∫ t in a..b, (γ t - z₀)⁻¹ * deriv γ t = 2 * Real.pi * I * n := by
    have h1 : ∫ t in a..b, (γ t - z₀)⁻¹ * deriv γ t =
        ∫ t in a..b, I * (Complex.ofReal (deriv θ t)) := by
      congr 1; ext t; exact h_integrand t
    have h_pull : ∫ t in a..b, I * Complex.ofReal (deriv θ t) =
        I * ∫ t in a..b, Complex.ofReal (deriv θ t) := by
      simp_rw [← smul_eq_mul]; exact intervalIntegral.integral_smul I _
    rw [h1, h_pull]
    have h_ofReal_int : IntervalIntegrable
        (fun t => Complex.ofReal (deriv θ t))
        MeasureTheory.volume a b :=
      ⟨(hθ_deriv_cont.intervalIntegrable a b).1.ofReal,
       (hθ_deriv_cont.intervalIntegrable a b).2.ofReal⟩
    have h_ftc : ∫ t in a..b, Complex.ofReal (deriv θ t) = (θ b : ℂ) - (θ a : ℂ) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => hasDerivAt_ofReal_comp θ x (hθ_diff x)) h_ofReal_int
    rw [h_ftc,
      show (θ b : ℂ) - (θ a : ℂ) = ((θ b - θ a : ℝ) : ℂ) from
        by push_cast; ring,
      hθ_change]; push_cast; ring
  have h_S1 : ∀ t, ‖γ t - z₀‖ = 1 := by
    intro t; simp only [γ, add_sub_cancel_left, mul_comm I]; exact norm_exp_ofReal_mul_I _
  have hint_const : ∀ ε > 0, ε < 1 →
      (∫ t in a..b, if ‖γ t - z₀‖ > ε then (γ t - z₀)⁻¹ * deriv γ t else 0) =
      2 * Real.pi * I * n := by
    intro ε _ hε_lt
    have h_cond : ∀ t, ‖γ t - z₀‖ > ε := fun t => by rw [h_S1]; exact hε_lt
    have : (fun t => if ‖γ t - z₀‖ > ε then (γ t - z₀)⁻¹ * deriv γ t else 0) =
        fun t => (γ t - z₀)⁻¹ * deriv γ t := by
      ext t; simp only [h_cond t, ↓reduceIte]
    rw [this, h_integral]
  have hlim : Tendsto (fun ε =>
      ∫ t in a..b, if ‖γ t - z₀‖ > ε then (γ t - z₀)⁻¹ * deriv γ t else 0)
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * Real.pi * I * n)) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with ε hε
      exact (hint_const ε (mem_Ioo.mp hε).1 (mem_Ioo.mp hε).2).symm)
  unfold generalizedWindingNumber' cauchyPrincipalValue'
  have h_match : (fun ε => ∫ t in a..b,
      if ‖(fun t => γ t - z₀) t - 0‖ > ε then
        (fun x => x⁻¹) ((fun t => γ t - z₀) t) * deriv (fun t => γ t - z₀) t
      else 0) = (fun ε => ∫ t in a..b,
      if ‖γ t - z₀‖ > ε then (γ t - z₀)⁻¹ * deriv γ t else 0) := by
    ext ε; congr 1 with t; simp only [sub_zero, deriv_sub_const]
  simp only [h_match, hlim.limUnder_eq]
  have hpi_ne : (2 : ℂ) * Real.pi * I ≠ 0 := by
    simp [ne_eq, mul_eq_zero, Complex.ofReal_eq_zero, Real.pi_ne_zero, I_ne_zero]
  field_simp

end
