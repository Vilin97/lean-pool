/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.GaussianEnvelope
public import LeanPool.NavierStokesAndEuler.NavierStokes.TangentODE
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# Energy estimates for the viscous two-mode equation

The norm is the genuine Euclidean norm on `EuclideanSpace ℝ (Fin 2)`.
The auxiliary Hilbert-space lemmas derive an estimate from a differential
equation and an energy inequality; no propagator bound is assumed.
-/

namespace NavierStokes.ViscousPropagator

open Set Filter MeasureTheory
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Right derivative of the norm away from zero, obtained from the squared norm. -/
theorem hasDerivWithinAt_norm_of_ne_zero {u : ℝ → H} {u' : H} {s : Set ℝ} {t : ℝ}
    (hu : HasDerivWithinAt u u' s t) (hne : u t ≠ 0) :
    HasDerivWithinAt (fun x => ‖u x‖) (⟪u t, u'⟫_ℝ / ‖u t‖) s t := by
  have hn : ‖u t‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  have hs := hu.norm_sq.sqrt (pow_ne_zero 2 hn)
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]
    using hs

/-- A dissipative linear equation grows in norm by at most its integrated forcing.
The equation is required only as a right derivative on the finite interval. -/
theorem norm_le_initial_add_integral
    {a b : ℝ} {u f : ℝ → H} (A : ℝ → H →L[ℝ] H)
    (hu : ContinuousOn u (Icc a b)) (hf : Continuous f)
    (hode : ∀ t ∈ Ico a b,
      HasDerivWithinAt u (A t (u t) + f t) (Ici t) t)
    (hA : ∀ t ∈ Ico a b, ∀ x : H, ⟪x, A t x⟫_ℝ ≤ 0) :
    ∀ t ∈ Icc a b, ‖u t‖ ≤ ‖u a‖ + ∫ s in a..t, ‖f s‖ := by
  let B : ℝ → ℝ := fun t => ‖u a‖ + ∫ s in a..t, ‖f s‖
  have hB (t : ℝ) : HasDerivAt B ‖f t‖ t :=
    (intervalIntegral.integral_hasDerivAt_right (hf.norm.intervalIntegrable a t)
      (hf.norm.stronglyMeasurableAtFilter _ _) hf.norm.continuousAt).const_add ‖u a‖
  apply image_le_of_liminf_slope_right_le_deriv_boundary
    (continuous_norm.comp_continuousOn hu) (by simp [B])
    (fun t _ => (hB t).continuousAt.continuousWithinAt)
    (fun t _ => (hB t).hasDerivWithinAt)
  intro t ht r hr
  by_cases hz : u t = 0
  · have hd : HasDerivWithinAt u (f t) (Ici t) t := by
      simpa [hz] using hode t ht
    exact hd.liminf_right_slope_norm_le hr
  · have hn : 0 < ‖u t‖ := norm_pos_iff.mpr hz
    have hi : ⟪u t, A t (u t) + f t⟫_ℝ ≤ ‖u t‖ * ‖f t‖ := by
      rw [inner_add_right]
      exact (add_le_add (hA t ht (u t)) (real_inner_le_norm (u t) (f t))).trans_eq
        (zero_add _)
    have hdiv : ⟪u t, A t (u t) + f t⟫_ℝ / ‖u t‖ ≤ ‖f t‖ := by
      apply (div_le_iff₀ hn).2
      simpa only [mul_comm] using hi
    exact (hasDerivWithinAt_norm_of_ne_zero (hode t ht) hz).liminf_right_slope_le
      (lt_of_le_of_lt hdiv hr)

/-- Integrating-factor estimate from a quadratic-form bound on the actual operator.
`W` is a positive scalar solution of `W' = growth * W`; it is not a bound
assumed for the vector solution. -/
theorem weighted_norm_le_initial_add_integral
    {a b : ℝ} {u f : ℝ → H} (A : ℝ → H →L[ℝ] H)
    (growth W : ℝ → ℝ) (hWpos : ∀ t, 0 < W t)
    (hW : ∀ t, HasDerivAt W (growth t * W t) t)
    (hu : ContinuousOn u (Icc a b)) (hf : Continuous f)
    (hode : ∀ t ∈ Ico a b,
      HasDerivWithinAt u (A t (u t) + f t) (Ici t) t)
    (hA : ∀ t ∈ Ico a b, ∀ x : H,
      ⟪x, A t x⟫_ℝ ≤ growth t * ‖x‖ ^ 2) :
    ∀ t ∈ Icc a b,
      ‖u t‖ / W t ≤ ‖u a‖ / W a + ∫ s in a..t, ‖f s‖ / W s := by
  have hInv (t : ℝ) : HasDerivAt (fun s => (W s)⁻¹)
      (-growth t * (W t)⁻¹) t := by
    convert! (hW t).inv (ne_of_gt (hWpos t)) using 1
    field_simp [ne_of_gt (hWpos t)]
  have hcInv : Continuous (fun t => (W t)⁻¹) :=
    continuous_iff_continuousAt.mpr fun t => (hInv t).continuousAt
  let v : ℝ → H := fun t => (W t)⁻¹ • u t
  let F : ℝ → H := fun t => (W t)⁻¹ • f t
  let B : ℝ → H →L[ℝ] H := fun t => A t - growth t • ContinuousLinearMap.id ℝ H
  have hv : ContinuousOn v (Icc a b) := hcInv.continuousOn.smul hu
  have hF : Continuous F := hcInv.smul hf
  have hvode (t : ℝ) (ht : t ∈ Ico a b) :
      HasDerivWithinAt v (B t (v t) + F t) (Ici t) t := by
    convert! (hInv t).hasDerivWithinAt.smul (hode t ht) using 1
    dsimp [v, F, B]
    simp only [sub_apply, smul_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_add]
    module
  have hB (t : ℝ) (ht : t ∈ Ico a b) (x : H) : ⟪x, B t x⟫_ℝ ≤ 0 := by
    dsimp [B]
    simp only [sub_apply, smul_apply,
      ContinuousLinearMap.id_apply, inner_sub_right, inner_smul_right,
      real_inner_self_eq_norm_sq]
    linarith [hA t ht x]
  have hn (t : ℝ) (x : H) : ‖(W t)⁻¹ • x‖ = ‖x‖ / W t := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hWpos t)),
      div_eq_mul_inv, mul_comm]
  have h := norm_le_initial_add_integral B hv hF hvode hB
  dsimp [v, F] at h
  simpa only [hn] using h

/-- The useful pulse bound: a positive envelope absorbs the variable reference
growth, while the remaining nonnegative error contributes one exponential. -/
theorem norm_le_envelope_mul_integral
    {a b : ℝ} {u f : ℝ → H} (A : ℝ → H →L[ℝ] H)
    (rate P : ℝ → ℝ) {μ : ℝ} (hμ : 0 ≤ μ)
    (hPpos : ∀ t, 0 < P t) (hP : ∀ t, HasDerivAt P (rate t * P t) t)
    (hu : ContinuousOn u (Icc a b)) (hf : Continuous f)
    (hode : ∀ t ∈ Ico a b,
      HasDerivWithinAt u (A t (u t) + f t) (Ici t) t)
    (hA : ∀ t ∈ Ico a b, ∀ x : H,
      ⟪x, A t x⟫_ℝ ≤ (rate t + μ) * ‖x‖ ^ 2) :
    ∀ t ∈ Icc a b,
      ‖u t‖ ≤ Real.exp (μ * (t - a)) * P t *
        (‖u a‖ / P a + ∫ s in a..t, ‖f s‖ / P s) := by
  let W : ℝ → ℝ := fun t => P t * Real.exp (μ * (t - a))
  have hWpos (t : ℝ) : 0 < W t := mul_pos (hPpos t) (Real.exp_pos _)
  have hExp (t : ℝ) : HasDerivAt (fun s : ℝ => Real.exp (μ * (s - a)))
      (μ * Real.exp (μ * (t - a))) t := by
    convert! (((hasDerivAt_id t).sub_const a).const_mul μ).exp using 1
    simp only [id, mul_one]
    ring
  have hW (t : ℝ) : HasDerivAt W ((rate t + μ) * W t) t := by
    convert! (hP t).mul (hExp t) using 1
    dsimp [W]
    ring
  have hcP : Continuous P := continuous_iff_continuousAt.mpr fun t => (hP t).continuousAt
  have hcW : Continuous W := continuous_iff_continuousAt.mpr fun t => (hW t).continuousAt
  have hF := hf.norm.div hcP (fun t => ne_of_gt (hPpos t))
  have hFW := hf.norm.div hcW (fun t => ne_of_gt (hWpos t))
  have hbase := weighted_norm_le_initial_add_integral A (fun t => rate t + μ) W
    hWpos hW hu hf hode hA
  intro t ht
  have hint : (∫ s in a..t, ‖f s‖ / W s) ≤ ∫ s in a..t, ‖f s‖ / P s := by
    apply intervalIntegral.integral_mono_on ht.1
      (hFW.intervalIntegrable a t) (hF.intervalIntegrable a t)
    intro s hs
    have he : 1 ≤ Real.exp (μ * (s - a)) :=
      Real.one_le_exp_iff.mpr (mul_nonneg hμ (sub_nonneg.mpr hs.1))
    have hPW : P s ≤ W s := by
      dsimp [W]
      nlinarith [hPpos s]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (hPpos s) hPW
  have hWa : W a = P a := by simp [W]
  have h := hbase t ht
  rw [hWa] at h
  have hout : ‖u t‖ / W t ≤ ‖u a‖ / P a + ∫ s in a..t, ‖f s‖ / P s :=
    h.trans (add_le_add_right hint _)
  calc
    ‖u t‖ ≤ (‖u a‖ / P a + ∫ s in a..t, ‖f s‖ / P s) * W t :=
      (div_le_iff₀ (hWpos t)).mp hout
    _ = Real.exp (μ * (t - a)) * P t *
        (‖u a‖ / P a + ∫ s in a..t, ‖f s‖ / P s) := by
      dsimp [W]
      ring

/-- Interval-only forcing version. Clamping the source outside the interval
shows that no global extension hypothesis on the forcing is needed. -/
theorem norm_le_envelope_mul_integral_on
    {a b : ℝ} {u f : ℝ → H} (A : ℝ → H →L[ℝ] H)
    (rate P : ℝ → ℝ) {μ : ℝ} (hμ : 0 ≤ μ)
    (hPpos : ∀ t, 0 < P t) (hP : ∀ t, HasDerivAt P (rate t * P t) t)
    (hu : ContinuousOn u (Icc a b)) (hf : ContinuousOn f (Icc a b))
    (hode : ∀ t ∈ Ico a b,
      HasDerivWithinAt u (A t (u t) + f t) (Ici t) t)
    (hA : ∀ t ∈ Ico a b, ∀ x : H,
      ⟪x, A t x⟫_ℝ ≤ (rate t + μ) * ‖x‖ ^ 2) :
    ∀ t ∈ Icc a b,
      ‖u t‖ ≤ Real.exp (μ * (t - a)) * P t *
        (‖u a‖ / P a + ∫ s in a..t, ‖f s‖ / P s) := by
  by_cases hab : a ≤ b
  · let F : ℝ → H := fun s => f (projIcc a b hab s)
    have hF : Continuous F := hf.domRestrict.comp continuous_projIcc
    have hFeq (s : ℝ) (hs : s ∈ Icc a b) : F s = f s := by
      simp only [F, projIcc_of_mem hab hs]
    have hodeF (s : ℝ) (hs : s ∈ Ico a b) :
        HasDerivWithinAt u (A s (u s) + F s) (Ici s) s := by
      rw [hFeq s (Ico_subset_Icc_self hs)]
      exact hode s hs
    have h := norm_le_envelope_mul_integral A rate P hμ hPpos hP hu hF hodeF hA
    intro t ht
    have heq : (∫ s in a..t, ‖F s‖ / P s) = ∫ s in a..t, ‖f s‖ / P s := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le ht.1] at hs
      change ‖F s‖ / P s = ‖f s‖ / P s
      rw [hFeq s ⟨hs.1, hs.2.trans ht.2⟩]
    simpa only [heq] using h t ht
  · intro t ht
    exact False.elim (hab (ht.1.trans ht.2))

/-- A source bounded by `K * P` retains that envelope and costs at most the
slot length. The scalar `K` may be any prescribed small-scale power times weights. -/
theorem zero_initial_source_bound
    {a b K : ℝ} {u f : ℝ → H} (A : ℝ → H →L[ℝ] H)
    (rate P : ℝ → ℝ) {μ : ℝ} (hμ : 0 ≤ μ)
    (hPpos : ∀ t, 0 < P t) (hP : ∀ t, HasDerivAt P (rate t * P t) t)
    (hu : ContinuousOn u (Icc a b)) (hf : ContinuousOn f (Icc a b))
    (hode : ∀ t ∈ Ico a b,
      HasDerivWithinAt u (A t (u t) + f t) (Ici t) t)
    (hA : ∀ t ∈ Ico a b, ∀ x : H,
      ⟪x, A t x⟫_ℝ ≤ (rate t + μ) * ‖x‖ ^ 2)
    (hinit : u a = 0) (hsource : ∀ t ∈ Icc a b, ‖f t‖ ≤ K * P t) :
    ∀ t ∈ Icc a b,
      ‖u t‖ ≤ Real.exp (μ * (t - a)) * P t * (K * (t - a)) := by
  have hcP : Continuous P := continuous_iff_continuousAt.mpr fun t => (hP t).continuousAt
  have hq : ContinuousOn (fun s => ‖f s‖ / P s) (Icc a b) :=
    hf.norm.div hcP.continuousOn (fun s _ => ne_of_gt (hPpos s))
  have h := norm_le_envelope_mul_integral_on A rate P hμ hPpos hP hu hf hode hA
  intro t ht
  have hint : (∫ s in a..t, ‖f s‖ / P s) ≤ K * (t - a) := by
    have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
    have hi := intervalIntegral.integral_mono_on (μ := volume) ht.1
      ((hq.mono hsub).intervalIntegrable_of_Icc ht.1)
      (continuous_const.intervalIntegrable a t) (fun s hs =>
        (div_le_iff₀ (hPpos s)).mpr (hsource s (hsub hs)))
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using hi
  have hh := h t ht
  simp only [hinit, norm_zero, zero_div, zero_add] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hint
    (mul_nonneg (Real.exp_pos _).le (hPpos t).le))

/-- Existence and the weighted estimate are compatible consequences of the
actual continuous-coefficient ODE, with no assumed propagator. -/
theorem exists_solution_with_envelope_bound [CompleteSpace H]
    {a b : ℝ} (hab : a ≤ b) (A : ℝ → H →L[ℝ] H) (f : ℝ → H)
    (rate P : ℝ → ℝ) {μ : ℝ} (hμ : 0 ≤ μ)
    (hPpos : ∀ t, 0 < P t) (hP : ∀ t, HasDerivAt P (rate t * P t) t)
    (hcA : ContinuousOn A (Icc a b)) (hcf : ContinuousOn f (Icc a b))
    (hA : ∀ t ∈ Ico a b, ∀ x : H,
      ⟪x, A t x⟫_ℝ ≤ (rate t + μ) * ‖x‖ ^ 2) (x₀ : H) :
    ∃ u : ℝ → H, u a = x₀ ∧
      (∀ t ∈ Icc a b, HasDerivAt u (A t (u t) + f t) t) ∧
      ∀ t ∈ Icc a b, ‖u t‖ ≤ Real.exp (μ * (t - a)) * P t *
        (‖x₀‖ / P a + ∫ s in a..t, ‖f s‖ / P s) := by
  obtain ⟨u, hinit, hode⟩ := TangentODE.exists_linear_solution hab A f hcA hcf x₀
  refine ⟨u, hinit, hode, ?_⟩
  have hu : ContinuousOn u (Icc a b) :=
    fun t ht => (hode t ht).continuousAt.continuousWithinAt
  have h := norm_le_envelope_mul_integral_on A rate P hμ hPpos hP hu hcf
    (fun t ht => (hode t (Ico_subset_Icc_self ht)).hasDerivWithinAt) hA
  simpa only [hinit] using h

/-- The two real modal coordinates with their Euclidean, not product-sup, norm. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Reflection in the growing coordinate. -/
noncomputable def reflection : Plane →L[ℝ] Plane :=
  LinearMap.toContinuousLinearMap {
    toFun := fun x => !₂[x 0, -x 1]
    map_add' := by
      intro x y
      ext i
      fin_cases i <;> simp [add_comm]
    map_smul' := by
      intro c x
      ext i
      fin_cases i <;> simp }

/-- `diag(lam,-lam)` as a genuine continuous linear operator. -/
noncomputable def diagonal (lam : ℝ) : Plane →L[ℝ] Plane := lam • reflection

/-- The actual diagonalized coefficient, including scalar damping and error. -/
noncomputable def coefficient (lam damping : ℝ) (E : Plane →L[ℝ] Plane) :
    Plane →L[ℝ] Plane :=
  diagonal lam - damping • ContinuousLinearMap.id ℝ Plane + E

theorem plane_norm_sq (x : Plane) : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

theorem inner_diagonal (lam : ℝ) (x : Plane) :
    ⟪x, diagonal lam x⟫_ℝ = lam * ((x 0) ^ 2 - (x 1) ^ 2) := by
  simp [diagonal, reflection, PiLp.inner_apply, Fin.sum_univ_two, pow_two]
  ring

theorem diagonal_energy_le {lam : ℝ} (hlam : 0 ≤ lam) (x : Plane) :
    ⟪x, diagonal lam x⟫_ℝ ≤ lam * ‖x‖ ^ 2 := by
  rw [inner_diagonal, plane_norm_sq]
  nlinarith [mul_nonneg hlam (sq_nonneg (x 1))]

/-- Operator norm controls its quadratic form without losing the sign of damping. -/
theorem error_energy_le (E : H →L[ℝ] H) (x : H) :
    ⟪x, E x⟫_ℝ ≤ ‖E‖ * ‖x‖ ^ 2 := by
  calc
    ⟪x, E x⟫_ℝ ≤ ‖x‖ * ‖E x‖ := real_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖E‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (E.le_opNorm x) (norm_nonneg x)
    _ = ‖E‖ * ‖x‖ ^ 2 := by ring

/-- Energy bound for the actual two-mode coefficient. -/
theorem coefficient_energy_le {lam : ℝ} (hlam : 0 ≤ lam)
    (damping : ℝ) (E : Plane →L[ℝ] Plane) (x : Plane) :
    ⟪x, coefficient lam damping E x⟫_ℝ ≤ (lam - damping + ‖E‖) * ‖x‖ ^ 2 := by
  simp only [coefficient, add_apply, sub_apply,
    smul_apply, ContinuousLinearMap.id_apply, inner_add_right,
    inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
  nlinarith [diagonal_energy_le hlam x, error_energy_le E x]

/-- The exponential-integral envelope has the required scalar ODE exactly. -/
theorem hasDerivAt_envelope {rate : ℝ → ℝ} (hrate : Continuous rate)
    (midpoint t : ℝ) :
    HasDerivAt (GaussianEnvelope.envelope rate midpoint)
      (rate t * GaussianEnvelope.envelope rate midpoint t) t := by
  have h := (intervalIntegral.integral_hasDerivAt_right
    (hrate.intervalIntegrable midpoint t) (hrate.stronglyMeasurableAtFilter _ _)
    hrate.continuousAt).exp
  unfold GaussianEnvelope.envelope
  simpa only [mul_comm] using h

/-- The actual viscous two-mode estimate. The damping may be smaller than
the reference by `dampingError / S`, and the full operator error is at most
`matrixError / S`. Neither error is multiplied by the harmonic index. -/
theorem viscous_propagator_estimate
    {a b midpoint S dampingError matrixError : ℝ}
    (hS : 0 < S) (hdampingError : 0 ≤ dampingError) (hmatrixError : 0 ≤ matrixError)
    (lam damping referenceDamping rate : ℝ → ℝ)
    (E : ℝ → Plane →L[ℝ] Plane) {u f : ℝ → Plane}
    (hrate : Continuous rate)
    (hreference : ∀ t ∈ Ico a b, rate t = lam t - referenceDamping t)
    (hlam : ∀ t ∈ Ico a b, 0 ≤ lam t)
    (hdamping : ∀ t ∈ Ico a b, referenceDamping t - dampingError / S ≤ damping t)
    (hE : ∀ t ∈ Ico a b, ‖E t‖ ≤ matrixError / S)
    (hu : ContinuousOn u (Icc a b)) (hf : ContinuousOn f (Icc a b))
    (hode : ∀ t ∈ Ico a b, HasDerivWithinAt u
      (coefficient (lam t) (damping t) (E t) (u t) + f t) (Ici t) t) :
    ∀ t ∈ Icc a b,
      ‖u t‖ ≤ Real.exp (((dampingError + matrixError) / S) * (t - a)) *
        GaussianEnvelope.envelope rate midpoint t *
        (‖u a‖ / GaussianEnvelope.envelope rate midpoint a +
          ∫ s in a..t, ‖f s‖ / GaussianEnvelope.envelope rate midpoint s) := by
  apply norm_le_envelope_mul_integral_on
    (fun t => coefficient (lam t) (damping t) (E t)) rate
    (GaussianEnvelope.envelope rate midpoint)
    (div_nonneg (add_nonneg hdampingError hmatrixError) hS.le)
    (GaussianEnvelope.envelope_pos rate midpoint) (hasDerivAt_envelope hrate midpoint)
    hu hf hode
  intro t ht x
  apply (coefficient_energy_le (hlam t ht) (damping t) (E t) x).trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg ‖x‖)
  rw [hreference t ht, add_div]
  linarith [hdamping t ht, hE t ht]

/-- A nonzero integer harmonic only increases nonnegative fundamental damping. -/
theorem high_harmonic_damping {j : ℤ} (hj : j ≠ 0) {D d δ : ℝ}
    (hD : 0 ≤ D) (hd : d - δ ≤ D) : d - δ ≤ (j : ℝ) ^ 2 * D := by
  have hjZ : (1 : ℤ) ≤ j ^ 2 := by
    have := sq_pos_of_ne_zero hj
    omega
  have hjR : (1 : ℝ) ≤ (j : ℝ) ^ 2 := by exact_mod_cast hjZ
  exact hd.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hjR hD)

/-- The same constants work for every nonzero harmonic. -/
theorem high_harmonic_propagator_estimate
    {a b midpoint S dampingError matrixError : ℝ}
    (hS : 0 < S) (hdampingError : 0 ≤ dampingError) (hmatrixError : 0 ≤ matrixError)
    (lam fundamentalDamping referenceDamping rate : ℝ → ℝ)
    (E : ℝ → Plane →L[ℝ] Plane) {u f : ℝ → Plane} {j : ℤ} (hj : j ≠ 0)
    (hrate : Continuous rate)
    (hreference : ∀ t ∈ Ico a b, rate t = lam t - referenceDamping t)
    (hlam : ∀ t ∈ Ico a b, 0 ≤ lam t)
    (hD : ∀ t ∈ Ico a b, 0 ≤ fundamentalDamping t)
    (hdamping : ∀ t ∈ Ico a b,
      referenceDamping t - dampingError / S ≤ fundamentalDamping t)
    (hE : ∀ t ∈ Ico a b, ‖E t‖ ≤ matrixError / S)
    (hu : ContinuousOn u (Icc a b)) (hf : ContinuousOn f (Icc a b))
    (hode : ∀ t ∈ Ico a b, HasDerivWithinAt u
      (coefficient (lam t) ((j : ℝ) ^ 2 * fundamentalDamping t) (E t) (u t) + f t)
      (Ici t) t) :
    ∀ t ∈ Icc a b,
      ‖u t‖ ≤ Real.exp (((dampingError + matrixError) / S) * (t - a)) *
        GaussianEnvelope.envelope rate midpoint t *
        (‖u a‖ / GaussianEnvelope.envelope rate midpoint a +
          ∫ s in a..t, ‖f s‖ / GaussianEnvelope.envelope rate midpoint s) := by
  exact viscous_propagator_estimate hS hdampingError hmatrixError lam
    (fun t => (j : ℝ) ^ 2 * fundamentalDamping t) referenceDamping rate E hrate
    hreference hlam (fun t ht => high_harmonic_damping hj (hD t ht) (hdamping t ht))
    hE hu hf hode

/-- Homogeneous forward bound in the usual envelope-ratio form. -/
theorem homogeneous_viscous_propagator_estimate
    {a b midpoint S dampingError matrixError : ℝ}
    (hS : 0 < S) (hdampingError : 0 ≤ dampingError) (hmatrixError : 0 ≤ matrixError)
    (lam damping referenceDamping rate : ℝ → ℝ)
    (E : ℝ → Plane →L[ℝ] Plane) {u : ℝ → Plane}
    (hrate : Continuous rate)
    (hreference : ∀ t ∈ Ico a b, rate t = lam t - referenceDamping t)
    (hlam : ∀ t ∈ Ico a b, 0 ≤ lam t)
    (hdamping : ∀ t ∈ Ico a b, referenceDamping t - dampingError / S ≤ damping t)
    (hE : ∀ t ∈ Ico a b, ‖E t‖ ≤ matrixError / S)
    (hu : ContinuousOn u (Icc a b))
    (hode : ∀ t ∈ Ico a b, HasDerivWithinAt u
      (coefficient (lam t) (damping t) (E t) (u t)) (Ici t) t) :
    ∀ t ∈ Icc a b,
      ‖u t‖ ≤ Real.exp (((dampingError + matrixError) / S) * |t - a|) *
        (GaussianEnvelope.envelope rate midpoint t /
          GaussianEnvelope.envelope rate midpoint a) * ‖u a‖ := by
  have h := viscous_propagator_estimate (midpoint := midpoint)
    hS hdampingError hmatrixError lam damping
    referenceDamping rate E hrate hreference hlam hdamping hE hu
    (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : Plane)) (Icc a b))
    (fun t ht => by simpa only [add_zero] using hode t ht)
  intro t ht
  have hh := h t ht
  simp only [norm_zero, zero_div, intervalIntegral.integral_zero, add_zero] at hh
  rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
  convert! hh using 1
  ring

/-- The positive reference eigenvalue appearing in the Gaussian construction. -/
noncomputable def referenceEigenvalue (lam u ell t : ℝ) : ℝ :=
  lam / Real.sqrt (1 + (PulseGrowth.slotMagnitude u ell t) ^ 2)

/-- The fundamental damping fixed by the manuscript's choice of `B_s`. -/
noncomputable def referenceViscosity (lam u ell t : ℝ) : ℝ :=
  lam * (1 + (PulseGrowth.slotMagnitude u ell t) ^ 2) /
    ((1 + u ^ 2) * Real.sqrt (1 + u ^ 2))

theorem reference_rate_split (lam u ell t : ℝ) :
    GaussianEnvelope.referenceRate lam u ell t =
      referenceEigenvalue lam u ell t - referenceViscosity lam u ell t := rfl

theorem referenceEigenvalue_nonneg {lam : ℝ} (hlam : 0 ≤ lam) (u ell t : ℝ) :
    0 ≤ referenceEigenvalue lam u ell t :=
  div_nonneg hlam (Real.sqrt_nonneg _)

theorem continuous_referenceRate (lam u ell : ℝ) :
    Continuous (GaussianEnvelope.referenceRate lam u ell) :=
  continuous_iff_continuousAt.mpr fun t =>
    (GaussianEnvelope.hasDerivAt_referenceRate lam u ell t).continuousAt

/-- Concrete specialization to the same scalar reference used by
`GaussianEnvelope.reference_gaussian_bounds`. -/
theorem reference_pulse_propagator_estimate
    {a b S dampingError matrixError lam₀ u₀ ell : ℝ}
    (hS : 0 < S) (hdampingError : 0 ≤ dampingError) (hmatrixError : 0 ≤ matrixError)
    (hlam₀ : 0 ≤ lam₀) (damping : ℝ → ℝ)
    (E : ℝ → Plane →L[ℝ] Plane) {u f : ℝ → Plane}
    (hdamping : ∀ t ∈ Ico a b,
      referenceViscosity lam₀ u₀ ell t - dampingError / S ≤ damping t)
    (hE : ∀ t ∈ Ico a b, ‖E t‖ ≤ matrixError / S)
    (hu : ContinuousOn u (Icc a b)) (hf : ContinuousOn f (Icc a b))
    (hode : ∀ t ∈ Ico a b, HasDerivWithinAt u
      (coefficient (referenceEigenvalue lam₀ u₀ ell t) (damping t) (E t) (u t) + f t)
      (Ici t) t) :
    let P := GaussianEnvelope.envelope (GaussianEnvelope.referenceRate lam₀ u₀ ell) (ell / 2)
    ∀ t ∈ Icc a b,
      ‖u t‖ ≤ Real.exp (((dampingError + matrixError) / S) * (t - a)) * P t *
        (‖u a‖ / P a + ∫ s in a..t, ‖f s‖ / P s) := by
  exact viscous_propagator_estimate hS hdampingError hmatrixError
    (referenceEigenvalue lam₀ u₀ ell) damping (referenceViscosity lam₀ u₀ ell)
    (GaussianEnvelope.referenceRate lam₀ u₀ ell) E
    (continuous_referenceRate lam₀ u₀ ell)
    (fun t _ => reference_rate_split lam₀ u₀ ell t)
    (fun t _ => referenceEigenvalue_nonneg hlam₀ u₀ ell t) hdamping hE hu hf hode

omit [InnerProductSpace ℝ H] in
/-- The physical viscosity coefficient is nonnegative. -/
theorem fundamental_damping_nonneg {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (k : ℝ) (n : H) : 0 ≤ epsilon * k ^ 2 * ‖n‖ ^ 2 := by
  positivity

/-- On a slot of length at most `L * S`, the error exponential is uniformly
bounded independently of the small scale and of the harmonic index. -/
theorem slot_exponential_bound {C S L a t : ℝ}
    (hC : 0 ≤ C) (hS : 0 < S) (hslot : t - a ≤ L * S) :
    Real.exp ((C / S) * (t - a)) ≤ Real.exp (C * L) := by
  apply Real.exp_le_exp.mpr
  calc
    (C / S) * (t - a) ≤ (C / S) * (L * S) :=
      mul_le_mul_of_nonneg_left hslot (div_nonneg hC hS.le)
    _ = C * L := by
      field_simp

end NavierStokes.ViscousPropagator
