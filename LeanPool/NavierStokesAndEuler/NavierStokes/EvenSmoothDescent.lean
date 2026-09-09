/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.SmoothParameterIntegral
public import LeanPool.NavierStokesAndEuler.NavierStokes.SmoothCutoffs
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Algebra.Group.EvenFunction

@[expose] public section

/-!
# Descent of an even smooth curve through the square map

The regularized radial derivative is obtained from the integral Hadamard
formula, not from a convergent power series. Its iterates are the genuine
one-sided derivatives of `X ↦ f (sqrt X)`.
-/

noncomputable section

open Set Filter MeasureTheory Function
open scoped Topology ContDiff

namespace NavierStokes.EvenSmoothDescent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  WithTop.coe_le_coe.mpr le_top

private theorem nat_lt_infty (n : ℕ) : (n : WithTop ℕ∞) < ∞ :=
  WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)

omit [CompleteSpace E] in
theorem contDiff_iteratedDeriv {f : ℝ → E} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv n f) := by
  simpa only [iteratedDeriv_eq_iterate] using hf.iterate_deriv n

omit [CompleteSpace E] in
theorem iteratedDeriv_iteratedDeriv (f : ℝ → E) (m n : ℕ) :
    iteratedDeriv m (iteratedDeriv n f) = iteratedDeriv (m + n) f := by
  simp only [iteratedDeriv_eq_iterate, Function.iterate_add_apply]

noncomputable def average (f : ℝ → E) (x : ℝ) : E :=
  ∫ t in (0 : ℝ)..1, f (t * x)

omit [CompleteSpace E] in
theorem iteratedDeriv_scale {f : ℝ → E} (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (x t : ℝ) :
    iteratedDeriv n (fun y => f (t * y)) x = t ^ n • iteratedDeriv n f (t * x) :=
  congrFun (iteratedDeriv_comp_const_smul (hf.of_le (nat_le_infty n)) t) x

omit [CompleteSpace E] in
theorem continuous_scaled_jet {f : ℝ → E} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    Continuous (fun z : ℝ × ℝ => iteratedDeriv n (fun x => f (z.2 * x)) z.1) := by
  simp_rw [iteratedDeriv_scale hf]
  exact (continuous_snd.pow n).smul
    ((hf.continuous_iteratedDeriv n (nat_le_infty n)).comp
      (continuous_snd.mul continuous_fst))

omit [CompleteSpace E] in
theorem measurable_scaled_jet {f : ℝ → E} (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : ℝ) :
    AEStronglyMeasurable (fun t => iteratedDeriv n (fun y => f (t * y)) x)
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
  ((continuous_scaled_jet hf n).comp
    (continuous_const.prodMk continuous_id)).aestronglyMeasurable

omit [CompleteSpace E] in
theorem dominated_scaled_jet {f : ℝ → E} (hf : ContDiff ℝ ∞ f) :
    SmoothParameterIntegral.LocallyDominatedDeriv (fun x t => f (t * x))
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
  intro n x
  have hc : IsCompact (Metric.closedBall x 1 ×ˢ Icc (0 : ℝ) 1) :=
    (isCompact_closedBall x 1).prod isCompact_Icc
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn
    (continuous_scaled_jet hf n).continuousOn
  refine ⟨1, zero_lt_one, fun _ => C, integrable_const C, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  intro y hy
  exact hC (y, t) ⟨Metric.ball_subset_closedBall hy, ht.1.le, ht.2⟩

omit [CompleteSpace E] in
theorem contDiff_average {f : ℝ → E} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (average f) := by
  change ContDiff ℝ ∞ (fun x => ∫ t in (0 : ℝ)..1, f (t * x))
  have hs : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) 1),
      ContDiff ℝ ∞ (fun x => f (t * x)) :=
    Filter.Eventually.of_forall fun t => hf.comp (contDiff_const.mul contDiff_id)
  simpa only [average, intervalIntegral.integral_of_le zero_le_one] using
    SmoothParameterIntegral.contDiff_integral_of_iteratedDeriv hs
      (measurable_scaled_jet hf) (dominated_scaled_jet hf)

omit [CompleteSpace E] in
theorem iteratedDeriv_average {f : ℝ → E} (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (average f) x =
      ∫ t in (0 : ℝ)..1, t ^ n • iteratedDeriv n f (t * x) := by
  change iteratedDeriv n (fun y => ∫ t in (0 : ℝ)..1, f (t * y)) x = _
  have hs : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) 1),
      ContDiff ℝ ∞ (fun x => f (t * x)) :=
    Filter.Eventually.of_forall fun t => hf.comp (contDiff_const.mul contDiff_id)
  have h := SmoothParameterIntegral.iteratedDeriv_integral hs
    (measurable_scaled_jet hf) (dominated_scaled_jet hf) n x
  simp_rw [iteratedDeriv_scale hf] at h
  simpa only [average, intervalIntegral.integral_of_le zero_le_one] using h

theorem iteratedDeriv_average_zero {f : ℝ → E} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    iteratedDeriv n (average f) 0 = (1 / ((n : ℝ) + 1)) • iteratedDeriv n f 0 := by
  rw [iteratedDeriv_average hf]
  simp only [mul_zero]
  rw [intervalIntegral.integral_smul_const, integral_pow]
  simp

theorem average_deriv_identity {f : ℝ → E} (hf : ContDiff ℝ ∞ f) (x : ℝ) :
    x • average (deriv f) x = f x - f 0 := by
  rw [average, intervalIntegral.smul_integral_comp_mul_right, zero_mul, one_mul]
  exact intervalIntegral.integral_deriv_eq_sub
    (fun _ _ => (contDiff_infty_iff_deriv.mp hf).1 _)
    ((contDiff_infty_iff_deriv.mp hf).2.continuous.intervalIntegrable 0 x)

noncomputable def radialDerivative (f : ℝ → E) (x : ℝ) : E :=
  (1 / 2 : ℝ) • average (iteratedDeriv 2 f) x

omit [CompleteSpace E] in
theorem contDiff_radialDerivative {f : ℝ → E} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (radialDerivative f) :=
  (contDiff_average (contDiff_iteratedDeriv hf 2)).const_smul (1 / 2 : ℝ)

omit [CompleteSpace E] in
theorem even_iteratedDeriv_two {f : ℝ → E} (he : Function.Even f) :
    Function.Even (iteratedDeriv 2 f) := by
  have heq : (fun x => f (-x)) = f := funext he
  intro x
  have h := iteratedDeriv_comp_neg 2 f x
  rw [heq] at h
  simpa using h.symm

omit [CompleteSpace E] in
theorem even_average {f : ℝ → E} (he : Function.Even f) : Function.Even (average f) := by
  intro x
  unfold average
  apply intervalIntegral.integral_congr
  intro t _
  change f (t * (-x)) = f (t * x)
  rw [mul_neg, he]

omit [CompleteSpace E] in
theorem even_radialDerivative {f : ℝ → E} (he : Function.Even f) :
    Function.Even (radialDerivative f) := by
  intro x
  exact congrArg ((1 / 2 : ℝ) • ·) (even_average (even_iteratedDeriv_two he) x)

omit [CompleteSpace E] in
theorem deriv_zero_of_even {f : ℝ → E} (he : Function.Even f) : deriv f 0 = 0 := by
  have heq : (fun x => f (-x)) = f := funext he
  have h := iteratedDeriv_comp_neg 1 f 0
  rw [heq] at h
  have hn : deriv f 0 = -(deriv f 0) := by simpa using h
  have hz : (2 : ℝ) • deriv f 0 = 0 := by
    calc
      (2 : ℝ) • deriv f 0 = deriv f 0 + deriv f 0 := two_smul ℝ (deriv f 0)
      _ = deriv f 0 + -(deriv f 0) := congrArg (fun v : E => deriv f 0 + v) hn
      _ = 0 := add_neg_cancel _
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

theorem radialDerivative_identity {f : ℝ → E} (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) (x : ℝ) :
    (2 * x) • radialDerivative f x = deriv f x := by
  have h := average_deriv_identity (contDiff_infty_iff_deriv.mp hf).2 x
  have htwo : iteratedDeriv 2 f = deriv (deriv f) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [radialDerivative, smul_smul, show 2 * x * (1 / 2 : ℝ) = x by ring, htwo]
  simpa only [deriv_zero_of_even he, sub_zero] using h

theorem radialDerivative_eq_div {f : ℝ → E} (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) {x : ℝ} (hx : x ≠ 0) :
    radialDerivative f x = (1 / (2 * x)) • deriv f x := by
  have h := congrArg (fun v : E => (2 * x)⁻¹ • v) (radialDerivative_identity hf he x)
  have hne : (2 : ℝ) * x ≠ 0 := mul_ne_zero (by norm_num) hx
  simpa only [smul_smul, inv_mul_cancel₀ hne, one_smul,
    one_div] using h

theorem iteratedDeriv_radialDerivative_zero {f : ℝ → E} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    iteratedDeriv n (radialDerivative f) 0 =
      (1 / (2 * ((n : ℝ) + 1))) • iteratedDeriv (n + 2) f 0 := by
  have ha := contDiff_average (contDiff_iteratedDeriv hf 2)
  change iteratedDeriv n ((1 / 2 : ℝ) • average (iteratedDeriv 2 f)) 0 = _
  rw [iteratedDeriv_const_smul (ha.of_le (nat_le_infty n)).contDiffAt,
    iteratedDeriv_average_zero (contDiff_iteratedDeriv hf 2), iteratedDeriv_iteratedDeriv,
    smul_smul]
  congr 1
  field_simp

noncomputable def descent (f : ℝ → E) (X : ℝ) : E := f (Real.sqrt X)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] in
theorem descent_square {f : ℝ → E} (he : Function.Even f) (x : ℝ) :
    descent f (x ^ 2) = f x := by
  rw [descent, Real.sqrt_sq_eq_abs]
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg hx, he]

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem continuous_descent {f : ℝ → E} (hf : Continuous f) : Continuous (descent f) :=
  hf.comp Real.continuous_sqrt

theorem hasDerivAt_descent_pos {f : ℝ → E} (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) {X : ℝ} (hX : 0 < X) :
    HasDerivAt (descent f) (descent (radialDerivative f) X) X := by
  have hd := ((contDiff_infty_iff_deriv.mp hf).1 (Real.sqrt X)).hasDerivAt.scomp X
    (Real.hasDerivAt_sqrt hX.ne')
  have hs : Real.sqrt X ≠ 0 := (Real.sqrt_pos.mpr hX).ne'
  change HasDerivAt (fun Y => f (Real.sqrt Y)) (radialDerivative f (Real.sqrt X)) X
  rw [radialDerivative_eq_div hf he hs]
  exact hd

theorem hasDerivWithinAt_descent_zero {f : ℝ → E} (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) :
    HasDerivWithinAt (descent f) (radialDerivative f 0) (Ici 0) 0 := by
  have hd : DifferentiableOn ℝ (descent f) (Ioi 0) :=
    fun X hX => (hasDerivAt_descent_pos hf he hX).differentiableAt.differentiableWithinAt
  have heq : deriv (descent f) =ᶠ[𝓝[>] 0] descent (radialDerivative f) := by
    filter_upwards [self_mem_nhdsWithin] with X hX
    exact (hasDerivAt_descent_pos hf he hX).deriv
  have ht : Tendsto (descent (radialDerivative f)) (𝓝[>] 0)
      (𝓝 (radialDerivative f 0)) := by
    simpa only [descent, Real.sqrt_zero] using
      ((continuous_descent (contDiff_radialDerivative hf).continuous).tendsto 0).mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  exact hasDerivWithinAt_Ici_of_tendsto_deriv hd
    (continuous_descent hf.continuous).continuousAt.continuousWithinAt
    self_mem_nhdsWithin (ht.congr' heq.symm)

theorem hasDerivWithinAt_descent {f : ℝ → E} (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) {X : ℝ} (hX : X ∈ Ici 0) :
    HasDerivWithinAt (descent f) (descent (radialDerivative f) X) (Ici 0) X := by
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ X from hX) with h | h
  · subst X
    simpa only [descent, Real.sqrt_zero] using hasDerivWithinAt_descent_zero hf he
  · exact (hasDerivAt_descent_pos hf he h).hasDerivWithinAt

noncomputable def radialIterate (f : ℝ → E) (n : ℕ) : ℝ → E :=
  (radialDerivative^[n]) f

omit [CompleteSpace E] in
theorem radialIterate_zero (f : ℝ → E) : radialIterate f 0 = f := rfl

omit [CompleteSpace E] in
theorem radialIterate_succ (f : ℝ → E) (n : ℕ) :
    radialIterate f (n + 1) = radialDerivative (radialIterate f n) :=
  Function.iterate_succ_apply' radialDerivative n f

omit [CompleteSpace E] in
theorem radialIterate_succ_right (f : ℝ → E) (n : ℕ) :
    radialIterate f (n + 1) = radialIterate (radialDerivative f) n :=
  Function.iterate_succ_apply radialDerivative n f

omit [CompleteSpace E] in
theorem contDiff_radialIterate {f : ℝ → E} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (radialIterate f n) := by
  induction n with
  | zero => exact hf
  | succ n ih => rw [radialIterate_succ]; exact contDiff_radialDerivative ih

omit [CompleteSpace E] in
theorem even_radialIterate {f : ℝ → E} (he : Function.Even f) (n : ℕ) :
    Function.Even (radialIterate f n) := by
  induction n with
  | zero => exact he
  | succ n ih => rw [radialIterate_succ]; exact even_radialDerivative ih

/-- The iterates of the regularized radial derivative are the actual
one-sided derivatives, including at the origin. -/
theorem iteratedDerivWithin_descent {f : ℝ → E} (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) (n : ℕ) :
    EqOn (iteratedDerivWithin n (descent f) (Ici 0)) (descent (radialIterate f n)) (Ici 0) := by
  induction n with
  | zero => intro X _; simp only [iteratedDerivWithin_zero, radialIterate_zero]
  | succ n ih =>
    intro X hX
    rw [iteratedDerivWithin_succ, derivWithin_congr ih (ih hX), radialIterate_succ]
    exact (hasDerivWithinAt_descent (contDiff_radialIterate hf n)
      (even_radialIterate he n) hX).derivWithin (uniqueDiffOn_Ici 0 X hX)

theorem contDiffOn_descent {f : ℝ → E} (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) : ContDiffOn ℝ ∞ (descent f) (Ici 0) := by
  apply contDiffOn_of_differentiableOn_deriv
  intro n _ X hX
  exact ((hasDerivWithinAt_descent (contDiff_radialIterate hf n)
    (even_radialIterate he n) hX).congr_of_mem
      (iteratedDerivWithin_descent hf he n) hX).differentiableWithinAt

theorem radialIterate_at_zero (n : ℕ) {f : ℝ → E} (hf : ContDiff ℝ ∞ f) :
    radialIterate f n 0 =
      ((n.factorial : ℝ) / ((2 * n).factorial : ℝ)) • iteratedDeriv (2 * n) f 0 := by
  induction n generalizing f with
  | zero => simp [radialIterate_zero]
  | succ n ih =>
    rw [radialIterate_succ_right, ih (contDiff_radialDerivative hf),
      iteratedDeriv_radialDerivative_zero hf, smul_smul]
    have hi : 2 * n + 2 = 2 * (n + 1) := by omega
    rw [hi]
    congr 1
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
      Nat.factorial_succ (2 * n + 1), Nat.factorial_succ (2 * n), Nat.factorial_succ n]
    push_cast
    field_simp ; ring

/-- Exact right jets of the descended function. -/
theorem iteratedDerivWithin_descent_zero {f : ℝ → E} (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) (n : ℕ) :
    iteratedDerivWithin n (descent f) (Ici 0) 0 =
      ((n.factorial : ℝ) / ((2 * n).factorial : ℝ)) • iteratedDeriv (2 * n) f 0 := by
  rw [iteratedDerivWithin_descent hf he n (show (0 : ℝ) ∈ Ici 0 from by simp)]
  simpa only [descent, Real.sqrt_zero] using radialIterate_at_zero n hf

/-! The local theorem uses an explicit cutoff extension. This extension is
constructed here; the input is not assumed to have a global even extension. -/

noncomputable def evenCutoff (r x : ℝ) : ℝ :=
  SmoothCutoffs.scaledCutoff (2 / r) x * SmoothCutoffs.scaledCutoff (2 / r) (-x)

noncomputable def localized (r : ℝ) (f : ℝ → E) (x : ℝ) : E :=
  evenCutoff r x • f x

theorem contDiff_evenCutoff (r : ℝ) : ContDiff ℝ ∞ (evenCutoff r) :=
  (SmoothCutoffs.scaledCutoff_contDiff (2 / r)).mul
    ((SmoothCutoffs.scaledCutoff_contDiff (2 / r)).comp contDiff_id.neg)

theorem even_evenCutoff (r : ℝ) : Function.Even (evenCutoff r) := by
  intro x
  simp only [evenCutoff, neg_neg, mul_comm]

theorem evenCutoff_eventually_one (r : ℝ) : evenCutoff r =ᶠ[𝓝 0] (fun _ => 1) := by
  have hn : (fun x => SmoothCutoffs.scaledCutoff (2 / r) (-x)) =ᶠ[𝓝 0] (fun _ => 1) :=
    (SmoothCutoffs.scaledCutoff_eventually_one_at_zero (2 / r)).comp_tendsto
      (by simpa using (continuous_neg.tendsto (0 : ℝ)))
  filter_upwards [SmoothCutoffs.scaledCutoff_eventually_one_at_zero (2 / r), hn]
    with x hx hn
  simp only [evenCutoff, hx, hn, mul_one]

omit [CompleteSpace E] in
theorem localized_eventuallyEq (r : ℝ) (f : ℝ → E) : localized r f =ᶠ[𝓝 0] f := by
  filter_upwards [evenCutoff_eventually_one r] with x hx
  simp only [localized, hx, one_smul]

private theorem one_lt_scaled_abs {r x : ℝ} (hr : 0 < r) (hx : r ≤ |x|) :
    1 < |(2 / r) * x| := by
  rw [abs_mul, abs_of_pos (div_pos (by norm_num) hr)]
  calc
    (1 : ℝ) < 2 := by norm_num
    _ = (2 / r) * r := by field_simp
    _ ≤ (2 / r) * |x| := mul_le_mul_of_nonneg_left hx (div_pos (by norm_num) hr).le

omit [CompleteSpace E] in
theorem localized_eventually_zero {r x : ℝ} (hr : 0 < r) (hx : r ≤ |x|) (f : ℝ → E) :
    localized r f =ᶠ[𝓝 x] (fun _ => 0) := by
  filter_upwards [SmoothCutoffs.scaledCutoff_eventually_zero (one_lt_scaled_abs hr hx)]
    with y hy
  simp only [localized, evenCutoff, hy, zero_mul, zero_smul]

omit [CompleteSpace E] in
theorem contDiff_localized {r : ℝ} (hr : 0 < r) {f : ℝ → E}
    (hf : ContDiffOn ℝ ∞ f (Ioo (-r) r)) : ContDiff ℝ ∞ (localized r f) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : |x| < r
  · exact (contDiff_evenCutoff r).contDiffAt.smul
      (hf.contDiffAt (isOpen_Ioo.mem_nhds (abs_lt.mp hx)))
  · exact contDiffAt_const.congr_of_eventuallyEq
      (localized_eventually_zero hr (le_of_not_gt hx) f)

omit [CompleteSpace E] in
theorem even_localized {r : ℝ} (hr : 0 < r) {f : ℝ → E}
    (he : ∀ x ∈ Ioo (-r) r, f (-x) = f x) : Function.Even (localized r f) := by
  intro x
  by_cases hx : |x| < r
  · change evenCutoff r (-x) • f (-x) = evenCutoff r x • f x
    rw [even_evenCutoff r x, he x (abs_lt.mp hx)]
  · have hx' : r ≤ |x| := le_of_not_gt hx
    have hnx : r ≤ |-x| := by simpa only [abs_neg] using hx'
    rw [(localized_eventually_zero hr hnx f).eq_of_nhds,
      (localized_eventually_zero hr hx' f).eq_of_nhds]

omit [CompleteSpace E] in
theorem descent_localized_eventuallyEq (r : ℝ) (f : ℝ → E) :
    descent (localized r f) =ᶠ[𝓝 0] descent f :=
  (localized_eventuallyEq r f).comp_tendsto
    (by simpa only [Real.sqrt_zero] using Real.continuous_sqrt.tendsto (0 : ℝ))

/-- Smoothness at the boundary requires only a smooth even germ on a symmetric
open interval. The global cutoff extension is constructed in the proof. -/
theorem contDiffWithinAt_descent_zero {r : ℝ} (hr : 0 < r) {f : ℝ → E}
    (hf : ContDiffOn ℝ ∞ f (Ioo (-r) r))
    (he : ∀ x ∈ Ioo (-r) r, f (-x) = f x) :
    ContDiffWithinAt ℝ ∞ (descent f) (Ici 0) 0 := by
  have hg := contDiffOn_descent (contDiff_localized hr hf) (even_localized hr he)
  have hEq := descent_localized_eventuallyEq r f
  exact (hg 0 (by simp)).congr_of_eventuallyEq
    (hEq.symm.filter_mono nhdsWithin_le_nhds) hEq.eq_of_nhds.symm

theorem contDiffOn_descent_local {r : ℝ} (hr : 0 < r) {f : ℝ → E}
    (hf : ContDiffOn ℝ ∞ f (Ioo (-r) r))
    (he : ∀ x ∈ Ioo (-r) r, f (-x) = f x) :
    ContDiffOn ℝ ∞ (descent f) (Ico 0 (r ^ 2)) := by
  intro X hX
  by_cases hz : X = 0
  · subst X
    exact (contDiffWithinAt_descent_zero hr hf he).mono Ico_subset_Ici_self
  · have hpos : 0 < X := lt_of_le_of_ne hX.1 (Ne.symm hz)
    have hsqrt : Real.sqrt X ∈ Ioo (-r) r := by
      constructor
      · linarith [Real.sqrt_nonneg X]
      · nlinarith [Real.sq_sqrt hX.1, Real.sqrt_nonneg X, hX.2]
    exact ((hf.contDiffAt (isOpen_Ioo.mem_nhds hsqrt)).comp X
      (Real.contDiffAt_sqrt hz)).contDiffWithinAt

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] in
theorem descent_square_local {r : ℝ} {f : ℝ → E}
    (he : ∀ x ∈ Ioo (-r) r, f (-x) = f x) {x : ℝ} (hx : x ∈ Ioo (-r) r) :
    descent f (x ^ 2) = f x := by
  rw [descent, Real.sqrt_sq_eq_abs]
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, he x hx]

/-- The exact endpoint jets of the local descent, using actual within
derivatives on the closed positive half-line. -/
theorem iteratedDerivWithin_descent_zero_local {r : ℝ} (hr : 0 < r) {f : ℝ → E}
    (hf : ContDiffOn ℝ ∞ f (Ioo (-r) r))
    (he : ∀ x ∈ Ioo (-r) r, f (-x) = f x) (n : ℕ) :
    iteratedDerivWithin n (descent f) (Ici 0) 0 =
      ((n.factorial : ℝ) / ((2 * n).factorial : ℝ)) • iteratedDeriv (2 * n) f 0 := by
  have h := iteratedDerivWithin_descent_zero
    (contDiff_localized hr hf) (even_localized hr he) n
  have hEq := descent_localized_eventuallyEq r f
  have hd : iteratedDerivWithin n (descent (localized r f)) (Ici 0) 0 =
      iteratedDerivWithin n (descent f) (Ici 0) 0 := by
    simp only [iteratedDerivWithin_eq_iteratedFDerivWithin]
    rw [(hEq.filter_mono nhdsWithin_le_nhds).iteratedFDerivWithin_eq hEq.eq_of_nhds n]
  rw [hd, (localized_eventuallyEq r f).iteratedDeriv_eq (2 * n)] at h
  exact h

end NavierStokes.EvenSmoothDescent
