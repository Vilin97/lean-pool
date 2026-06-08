/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import Mathlib.Geometry.Manifold.Notation
public import Mathlib.NumberTheory.ModularForms.QExpansion

public import LeanPool.LeanModularForms.Modularforms.AtImInfty
public import LeanPool.LeanModularForms.Modularforms.SlashActionAuxil

/-! # ResToImagAxis -/


@[expose] public section

open UpperHalfPlane hiding I

open Real Complex ContinuousMap Matrix CongruenceSubgroup ModularGroup Filter Asymptotics

open scoped Interval Real Topology Manifold ModularForm MatrixGroups

/--
Restrict a function `F : ℍ → ℂ` to the positive imaginary axis, i.e. `t ↦ F (I * t)`.
If $t \le 0$, then `F (I * t)` is not defined, and we return `0` in that case.
-/
noncomputable def ResToImagAxis (F : ℍ → ℂ) : ℝ → ℂ :=
  fun t => if ht : 0 < t then F ⟨(I * t), by simp [ht]⟩ else 0

namespace Function

/-- Dot notation alias for `ResToImagAxis`. -/
noncomputable def resToImagAxis (F : ℍ → ℂ) : ℝ → ℂ := ResToImagAxis F

@[simp] lemma resToImagAxis_eq_resToImagAxis (F : ℍ → ℂ) :
    F.resToImagAxis = ResToImagAxis F := rfl

@[simp] lemma resToImagAxis_apply (F : ℍ → ℂ) (t : ℝ) :
    F.resToImagAxis t = ResToImagAxis F t := rfl

end Function

/--
Function $F : \mathbb{H} \to \mathbb{C}$ whose restriction to the imaginary axis is real-valued,
i.e. imaginary part is zero.
-/
@[fun_prop]
noncomputable def ResToImagAxis.Real (F : ℍ → ℂ) : Prop :=
  ∀ t : ℝ, 0 < t → (F.resToImagAxis t).im = 0

/--
Function $F : \mathbb{H} \to \mathbb{C}$ is real and positive on the imaginary axis.
-/
@[fun_prop]
noncomputable def ResToImagAxis.Pos (F : ℍ → ℂ) : Prop :=
  ResToImagAxis.Real F ∧ ∀ t : ℝ, 0 < t → 0 < (F.resToImagAxis t).re

/--
Function $F : \mathbb{H} \to \mathbb{C}$ whose restriction to the imaginary axis is eventually
positive, i.e. there exists $t_0 > 0$ such that for all $t \ge t_0$, $F(it)$ is real and positive.
-/
@[fun_prop]
noncomputable def ResToImagAxis.EventuallyPos (F : ℍ → ℂ) : Prop :=
  ResToImagAxis.Real F ∧ ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, t₀ ≤ t → 0 < (F.resToImagAxis t).re

@[fun_prop]
theorem ResToImagAxis.Differentiable (F : ℍ → ℂ) (hF : MDiff F) (t : ℝ)
    (ht : 0 < t) : DifferentiableAt ℝ F.resToImagAxis t := by
  rw [Function.resToImagAxis_eq_resToImagAxis]
  have hcdiff := hF ⟨Complex.I * t, by norm_num [Complex.I_re, ht]⟩
  rw [mdifferentiableAt_iff] at hcdiff
  have h_diff :
      DifferentiableAt ℝ (fun t : ℝ => F (ofComplex (Complex.I * t))) t := by
    haveI : IsScalarTower ℝ ℂ ℂ := IsScalarTower.complexToReal
    convert hcdiff.restrictScalars ℝ |> DifferentiableAt.comp t <|
      DifferentiableAt.const_mul ofRealCLM.differentiableAt _ using 1
  apply h_diff.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds ht] with t ht
  simp_all only [ResToImagAxis, ↓reduceDIte]
  rw [ofComplex_apply_of_im_pos]

/--
Restriction and slash action under S: $(F |_k S) (it) = (it)^{-k} * F(it)$
-/
theorem ResToImagAxis.SlashActionS (F : ℍ → ℂ) (k : ℤ) {t : ℝ} (ht : 0 < t) :
    (F ∣[k] S).resToImagAxis t = (Complex.I) ^ (-k) * t ^ (-k) * F.resToImagAxis (1 / t) := by
  set z : ℍ := ⟨I * t, by simp [ht]⟩ with hzdef
  set z' : ℍ := ⟨I * (1 / t : ℝ), by simpa [one_div_pos.2 ht]⟩ with hz'def
  have h : mk (-z)⁻¹ z.im_inv_neg_coe_pos = z' :=
    UpperHalfPlane.ext (by simp [hzdef, hz'def, mul_comm])
  simpa [ResToImagAxis, ht, hz'def] using (by
    rw [modular_slash_S_apply, h]; simp [hzdef, mul_zpow I (t : ℂ) (-k), mul_comm (F z')] :
    (F ∣[k] S) z = I ^ (-k) * t ^ (-k) * F z')

/--
Realness, positivity and essential positivity are closed under the addition and multiplication.
-/
@[fun_prop]
theorem ResToImagAxis.Real.const (c : ℝ) : ResToImagAxis.Real (fun _ => c) := by
  intro t ht
  simp only [Function.resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte, ofReal_im]

@[fun_prop]
theorem ResToImagAxis.Real.zero : ResToImagAxis.Real (fun _ => 0) := ResToImagAxis.Real.const 0

@[fun_prop]
theorem ResToImagAxis.Real.one : ResToImagAxis.Real (fun _ => 1) := ResToImagAxis.Real.const 1

@[fun_prop]
theorem ResToImagAxis.Real.neg {F : ℍ → ℂ} (hF : ResToImagAxis.Real F) : ResToImagAxis.Real (-F)
    := by
  intro t ht
  have hFreal := hF t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hFreal
  simp [ResToImagAxis, ht, hFreal]

@[fun_prop]
theorem ResToImagAxis.Real.add {F G : ℍ → ℂ} (hF : ResToImagAxis.Real F)
    (hG : ResToImagAxis.Real G) : ResToImagAxis.Real (F + G) := by
  intro t ht
  have hFreal := hF t ht
  have hGreal := hG t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hFreal hGreal
  simp [ResToImagAxis, ht, hFreal, hGreal]

@[fun_prop]
theorem ResToImagAxis.Real.sub {F G : ℍ → ℂ} (hF : ResToImagAxis.Real F)
    (hG : ResToImagAxis.Real G) : ResToImagAxis.Real (F - G) := by
  simpa [sub_eq_add_neg] using ResToImagAxis.Real.add hF hG.neg

@[fun_prop]
theorem ResToImagAxis.Real.mul {F G : ℍ → ℂ} (hF : ResToImagAxis.Real F)
    (hG : ResToImagAxis.Real G) : ResToImagAxis.Real (F * G) := by
  intro t ht
  have hFreal := hF t ht
  have hGreal := hG t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hFreal hGreal
  simp [ResToImagAxis, ht, hFreal, hGreal]

@[fun_prop]
theorem ResToImagAxis.Real.smul {F : ℍ → ℂ} {c : ℝ} (hF : ResToImagAxis.Real F) :
    ResToImagAxis.Real (c • F) := by
  intro t ht
  have hFreal := hF t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hFreal
  simp [ResToImagAxis, ht, hFreal]

@[fun_prop]
theorem ResToImagAxis.Real.pow {F : ℍ → ℂ} (hF : ResToImagAxis.Real F) (n : ℕ) :
    ResToImagAxis.Real (F ^ n) := by
  induction n with
  | zero => exact ResToImagAxis.Real.one
  | succ n hn => exact hn.mul hF

theorem ResToImagAxis.Pos.const (c : ℝ) (hc : 0 < c) : ResToImagAxis.Pos (fun _ => c) :=
  ⟨ResToImagAxis.Real.const c, fun t ht ↦ by simp [ResToImagAxis, ht, hc]⟩

@[fun_prop]
theorem ResToImagAxis.Pos.one : ResToImagAxis.Pos (fun _ => 1) :=
  ResToImagAxis.Pos.const 1 one_pos

@[fun_prop]
theorem ResToImagAxis.Pos.add {F G : ℍ → ℂ} (hF : ResToImagAxis.Pos F)
    (hG : ResToImagAxis.Pos G) : ResToImagAxis.Pos (F + G) := by
  rw [Pos]
  refine ⟨Real.add hF.1 hG.1, fun t ht ↦ ?_⟩
  have hFpos := hF.2 t ht
  have hGpos := hG.2 t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hFpos hGpos
  simp [ResToImagAxis, ht, add_pos hFpos hGpos]

@[fun_prop]
theorem ResToImagAxis.Pos.mul {F G : ℍ → ℂ} (hF : ResToImagAxis.Pos F)
    (hG : ResToImagAxis.Pos G) : ResToImagAxis.Pos (F * G) := by
  rw [Pos]
  refine ⟨Real.mul hF.1 hG.1, fun t ht ↦ ?_⟩
  have hFreal := hF.1 t ht
  have hGreal := hG.1 t ht
  have hFpos := hF.2 t ht
  have hGpos := hG.2 t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hFreal hGreal
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hFpos hGpos
  simp [ResToImagAxis, ht, hFreal, hGreal, mul_pos hFpos hGpos]

@[fun_prop]
theorem ResToImagAxis.Pos.smul {F : ℍ → ℂ} {c : ℝ} (hF : ResToImagAxis.Pos F)
    (hc : 0 < c) : ResToImagAxis.Pos (c • F) := by
  rw [Pos]
  refine ⟨Real.smul hF.1, fun t ht ↦ ?_⟩
  have hFreal := hF.1 t ht
  have hFpos := hF.2 t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hFreal
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hFpos
  simp [ResToImagAxis, ht, mul_pos hc hFpos]

@[fun_prop]
theorem ResToImagAxis.Pos.pow {F : ℍ → ℂ} (hF : ResToImagAxis.Pos F) (n : ℕ) :
    ResToImagAxis.Pos (F ^ n) := by
  induction n with
  | zero => exact ResToImagAxis.Pos.one
  | succ n hn => exact hn.mul hF

@[fun_prop]
theorem ResToImagAxis.EventuallyPos.from_pos {F : ℍ → ℂ} (hF : ResToImagAxis.Pos F) :
    ResToImagAxis.EventuallyPos F := by
  refine ⟨hF.1, ⟨1, by positivity, fun t ht ↦ ?_⟩⟩
  have ht_pos : 0 < t := by linarith
  exact hF.2 t ht_pos

@[fun_prop]
theorem ResToImagAxis.EventuallyPos.one :
    ResToImagAxis.EventuallyPos (fun _ => 1) :=
  ResToImagAxis.EventuallyPos.from_pos ResToImagAxis.Pos.one

@[fun_prop]
theorem ResToImagAxis.EventuallyPos.const (c : ℝ) (hc : 0 < c) :
    ResToImagAxis.EventuallyPos (fun _ => c) :=
  ResToImagAxis.EventuallyPos.from_pos (ResToImagAxis.Pos.const c hc)

@[fun_prop]
theorem ResToImagAxis.EventuallyPos.add {F G : ℍ → ℂ}
    (hF : ResToImagAxis.EventuallyPos F) (hG : ResToImagAxis.EventuallyPos G) :
    ResToImagAxis.EventuallyPos (F + G) := by
  rw [EventuallyPos]
  refine ⟨ResToImagAxis.Real.add hF.1 hG.1, ?_⟩
  obtain ⟨tF, hF0, hFpos⟩ := hF.2
  obtain ⟨tG, hG0, hGpos⟩ := hG.2
  let t₀ := max tF tG
  use t₀
  refine ⟨by positivity, fun t ht ↦ ?_⟩
  have htF₀ : tF ≤ t₀ := by grind
  have htG₀ : tG ≤ t₀ := by grind
  have htF : tF ≤ t := htF₀.trans ht
  have htG : tG ≤ t := htG₀.trans ht
  have hFpos_t := hFpos t htF
  have hGpos_t := hGpos t htG
  have htpos : 0 < t := by grind
  simp only [Function.resToImagAxis_apply, ResToImagAxis, htpos] at hFpos_t hGpos_t
  simp only [Function.resToImagAxis_apply, ResToImagAxis, htpos]
  exact add_pos hFpos_t hGpos_t

@[fun_prop]
theorem ResToImagAxis.EventuallyPos.mul {F G : ℍ → ℂ}
    (hF : ResToImagAxis.EventuallyPos F) (hG : ResToImagAxis.EventuallyPos G) :
    ResToImagAxis.EventuallyPos (F * G) := by
  rw [EventuallyPos]
  refine ⟨ResToImagAxis.Real.mul hF.1 hG.1, ?_⟩
  obtain ⟨tF, hF0, hFpos⟩ := hF.2
  obtain ⟨tG, hG0, hGpos⟩ := hG.2
  let t₀ := max tF tG
  use t₀
  refine ⟨by positivity, fun t ht ↦ ?_⟩
  have htpos : 0 < t := by grind
  have hFreal_t := hF.1 t htpos
  have hGreal_t := hG.1 t htpos
  have htF₀ : tF ≤ t₀ := by grind
  have htG₀ : tG ≤ t₀ := by grind
  have htF : tF ≤ t := htF₀.trans ht
  have htG : tG ≤ t := htG₀.trans ht
  have hFpos_t := hFpos t htF
  have hGpos_t := hGpos t htG
  simp only [Function.resToImagAxis, ResToImagAxis, htpos] at hFpos_t hGpos_t
  simp only [Function.resToImagAxis, ResToImagAxis, htpos, ↓reduceDIte] at hFreal_t hGreal_t
  simp only [Function.resToImagAxis_apply, ResToImagAxis, htpos, ↓reduceDIte, Pi.mul_apply, mul_re,
    hFreal_t, hGreal_t, mul_zero, sub_zero]
  exact mul_pos hFpos_t hGpos_t

@[fun_prop]
theorem ResToImagAxis.EventuallyPos.pow {F : ℍ → ℂ}
    (hF : ResToImagAxis.EventuallyPos F) (n : ℕ) :
    ResToImagAxis.EventuallyPos (F ^ n) := by
  induction n with
  | zero => exact ResToImagAxis.EventuallyPos.one
  | succ n hn => exact hn.mul hF

@[fun_prop]
theorem ResToImagAxis.EventuallyPos.smul {F : ℍ → ℂ} {c : ℝ} (hF : ResToImagAxis.EventuallyPos F)
    (hc : 0 < c) : ResToImagAxis.EventuallyPos (c • F) := by
  rw [EventuallyPos]
  refine ⟨ResToImagAxis.Real.smul hF.1, ?_⟩
  obtain ⟨t₀, hF0, hFpos⟩ := hF.2
  use t₀
  refine ⟨hF0, fun t ht ↦ ?_⟩
  have htpos : 0 < t := by grind
  have hFreal_t := hF.1 t htpos
  have hFpos_t := hFpos t ht
  simp only [Function.resToImagAxis, ResToImagAxis, htpos, ↓reduceDIte] at hFreal_t
  simp only [Function.resToImagAxis, ResToImagAxis, htpos, ↓reduceDIte] at hFpos_t
  simp [ResToImagAxis, htpos, mul_pos hc hFpos_t]

/-- If `F` is real-valued, then `F` is equal to the real part of itself on imaginary axis. -/
theorem ResToImagAxis.Real.eq_real_part {F : ℍ → ℂ} (hF : ResToImagAxis.Real F) (t : ℝ) :
    F.resToImagAxis t = (F.resToImagAxis t).re := by
  simp only [Function.resToImagAxis, ResToImagAxis]
  split_ifs with ht
  exacts [Complex.ext rfl (by simpa [Function.resToImagAxis, ResToImagAxis, ht]
    using (hF t ht)), rfl]

/-!
## Polynomial decay of functions with exponential bounds

This section establishes that if a function `F : ℍ → ℂ` is `O(exp(-c * im τ))` at infinity,
then `t^s * F(it) → 0` as `t → ∞` for any real power `s`.

One application is to cusp forms, which satisfy such exponential decay bounds.
-/

/--
If `F : ℍ → ℂ` is `O(exp(-c * im τ))` at `atImInfty` for some `c > 0`, then
the restriction to the imaginary axis `t ↦ F(it)` is `O(exp(-c * t))` at `atTop`.
-/
lemma isBigO_resToImagAxis_of_isBigO_atImInfty {F : ℍ → ℂ} {c : ℝ} (_hc : 0 < c)
    (hF : F =O[atImInfty] fun τ => Real.exp (-c * τ.im)) :
    F.resToImagAxis =O[atTop] fun t => Real.exp (-c * t) := by
  rw [Asymptotics.isBigO_iff] at hF ⊢
  obtain ⟨C, hC⟩ := hF; use C
  rw [Filter.eventually_atImInfty] at hC; obtain ⟨A, hA⟩ := hC
  filter_upwards [Filter.eventually_ge_atTop (max A 1)] with t ht
  have ht_pos : 0 < t := lt_of_lt_of_le one_pos (le_of_max_le_right ht)
  simp only [Function.resToImagAxis, ResToImagAxis, ht_pos, ↓reduceDIte]
  set z : ℍ := ⟨Complex.I * t, by simp [ht_pos]⟩
  have him : z.im = t := by change (Complex.I * t).im = t; simp
  simpa [him] using hA z (by simpa [him] using le_of_max_le_left ht)

/--
The analytic kernel: if `g : ℝ → ℂ` is eventually bounded by `C * exp(-b * t)` for some
`b > 0`, then `t^s * g(t) → 0` as `t → ∞` for any real power `s`.

This follows from the fact that `t^s * exp(-b * t) → 0` (mathlib's
`tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`) combined with the big-O transfer lemma.
-/
lemma tendsto_rpow_mul_of_isBigO_exp {g : ℝ → ℂ} {s b : ℝ} (hb : 0 < b)
    (hg : g =O[atTop] fun t => rexp (-b * t)) :
    Tendsto (fun t : ℝ => (t : ℂ) ^ (s : ℂ) * g t) atTop (𝓝 0) := by
  refine ((isBigO_refl _ _).mul (Complex.isBigO_ofReal_right.mpr hg)).trans_tendsto ?_
  refine (tendsto_ofReal_iff.mpr (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s b hb)).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [Complex.ofReal_mul, Complex.ofReal_cpow (le_of_lt ht)]

/--
If `F : ℍ → ℂ` is `O(exp(-c * im τ))` at `atImInfty` for some `c > 0`, then
`t^s * F(it) → 0` as `t → ∞` for any real power `s`.
-/
theorem tendsto_rpow_mul_resToImagAxis_of_isBigO_exp {F : ℍ → ℂ} {c : ℝ} (hc : 0 < c)
    (hF : F =O[atImInfty] fun τ => rexp (-c * τ.im)) (s : ℝ) :
    Tendsto (fun t : ℝ => (t : ℂ) ^ (s : ℂ) * F.resToImagAxis t) atTop (𝓝 0) :=
  tendsto_rpow_mul_of_isBigO_exp hc (isBigO_resToImagAxis_of_isBigO_atImInfty hc hF)

/--
For a cusp form `f` of level `Γ(n)`, we have `t^s * f(it) → 0` as `t → ∞` for any real power `s`.

This follows from the exponential decay of cusp forms at infinity: `f = O(exp(-2π τ.im / n))`.
-/
theorem cuspForm_rpow_mul_resToImagAxis_tendsto_zero {n : ℕ} {k : ℤ} {F : Type*}
    [NeZero n] [FunLike F ℍ ℂ] [CuspFormClass F Γ(n) k] (f : F) (s : ℝ) :
    Tendsto (fun t : ℝ => (t : ℂ) ^ (s : ℂ) * (f : ℍ → ℂ).resToImagAxis t) atTop (𝓝 0) := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  have hmem : (n : ℝ) ∈ (Γ(n) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simp only [strictPeriods_Gamma]
    exact AddSubgroup.mem_zmultiples (n : ℝ)
  have hdecay' : (f : ℍ → ℂ) =O[atImInfty] fun τ => rexp (-(2 * π / n) * τ.im) := by
    convert CuspFormClass.exp_decay_atImInfty hn_pos hmem (f := f) using 2 with τ; field_simp
  exact tendsto_rpow_mul_resToImagAxis_of_isBigO_exp (div_pos (by positivity) hn_pos) hdecay' s

/-!
## Fourier expansion approach for polynomial decay

This section provides an alternative approach to polynomial decay that works directly from
Fourier expansions. If `F` has a Fourier expansion `∑_{m≥0} a_m exp(2πi(m+n₀)z)` with `n₀ > 0`,
then `F = O(exp(-2π n₀ · im z))` at `atImInfty`, which gives `t^s * F(it) → 0`.

This is useful for functions with q-expansions starting at a positive index (like `(E₂E₄ - E₆)²`).
-/

/--
If `F` has a Fourier expansion `∑_{m≥0} a_m exp(2πi(m+n₀)z)` with `n₀ > 0`,
and the coefficients are absolutely summable at height `im z = c`,
then `F = O(exp(-2π n₀ · im z))` at `atImInfty`.

The key bound is: for `im z ≥ c`,
  `‖F(z)‖ ≤ (∑_m ‖a_m‖ · exp(-2π c m)) · exp(-2π n₀ · im z)`
-/
lemma isBigO_atImInfty_of_fourier_shift
    {F : ℍ → ℂ} {a : ℕ → ℂ} {n₀ : ℕ} {c : ℝ} (_hn₀ : 0 < n₀) (_hc : 0 < c)
    (hF : ∀ z : ℍ, F z =
      ∑' m : ℕ, a m * cexp (2 * π * I * ((m + n₀ : ℕ) : ℂ) * (z : ℂ)))
    (ha : Summable (fun m : ℕ => ‖a m‖ * rexp (-(2 * π * c) * (m : ℝ)))) :
    F =O[atImInfty] fun z : ℍ => rexp (-(2 * π * (n₀ : ℝ)) * z.im) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨∑' m, ‖a m‖ * rexp (-(2 * π * c) * m), ?_⟩
  rw [Filter.eventually_atImInfty]
  refine ⟨c, fun z hz => ?_⟩
  rw [hF z, Real.norm_of_nonneg (le_of_lt (Real.exp_pos _))]
  -- Real part of 2πi(m+n₀)z is -2π(m+n₀)·im z
  have hexp_re m : (2 * π * I * ((m + n₀ : ℕ) : ℂ) * z).re = -(2 * π) * (m + n₀) * z.im := by
    simp only [Nat.cast_add, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero,
      Complex.I_re, mul_im, zero_mul, add_zero, Complex.I_im, mul_one, sub_self, add_re, natCast_re,
      add_im, natCast_im, coe_re, zero_add, coe_im, zero_sub, neg_mul]
  -- Key bound: for y ≥ c, exp(-(2π)(m+n₀)y) ≤ exp(-(2πc)m) * exp(-(2πc)n₀)
  have hexp_bound (m : ℕ) :
      rexp (-(2 * π) * (↑m + ↑n₀) * z.im) ≤
        rexp (-(2 * π * c) * m) * rexp (-(2 * π * c) * n₀) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have _ : (↑m + ↑n₀) * z.im ≥ (↑m + ↑n₀) * c := by nlinarith
    nlinarith [Real.pi_pos, (Nat.cast_nonneg m : (0 : ℝ) ≤ m),
      (Nat.cast_nonneg n₀ : (0 : ℝ) ≤ n₀), z.im_pos]
  -- Summability of norms
  have hsum_norms : Summable fun m => ‖a m * cexp (2 * π * I * ((m + n₀ : ℕ) : ℂ) * z)‖ := by
    refine .of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
      (ha.mul_right (rexp (-(2 * π * c) * n₀)))
    simp only [norm_mul, norm_exp, hexp_re]
    calc ‖a m‖ * rexp (-(2 * π) * (↑m + ↑n₀) * z.im)
        ≤ ‖a m‖ * (rexp (-(2 * π * c) * m) * rexp (-(2 * π * c) * n₀)) :=
          mul_le_mul_of_nonneg_left (hexp_bound m) (norm_nonneg _)
      _ = ‖a m‖ * rexp (-(2 * π * c) * m) * rexp (-(2 * π * c) * n₀) := by ring
  have hsum_norms' : Summable fun m => ‖a m‖ * rexp (-(2 * π) * (m + n₀) * z.im) := by
    convert hsum_norms with m; rw [norm_mul, norm_exp, hexp_re]
  -- Main calculation
  calc ‖∑' m, a m * cexp (2 * π * I * ((m + n₀ : ℕ) : ℂ) * z)‖
      ≤ ∑' m, ‖a m * cexp (2 * π * I * ((m + n₀ : ℕ) : ℂ) * z)‖ :=
        norm_tsum_le_tsum_norm hsum_norms
    _ = ∑' m, ‖a m‖ * rexp (-(2 * π) * (m + n₀) * z.im) := by
        simp only [norm_mul, norm_exp, hexp_re]
    _ ≤ ∑' m, ‖a m‖ * rexp (-(2 * π * c) * m) * rexp (-(2 * π) * n₀ * z.im) := by
        refine Summable.tsum_le_tsum (fun m => ?_) hsum_norms'
          (ha.mul_right (rexp (-(2 * π) * n₀ * z.im)))
        have hsplit : rexp (-(2 * π) * (↑m + ↑n₀) * z.im) =
            rexp (-(2 * π) * m * z.im) * rexp (-(2 * π) * n₀ * z.im) := by
          rw [← Real.exp_add]; ring_nf
        have hexp_m : rexp (-(2 * π) * m * z.im) ≤ rexp (-(2 * π * c) * m) := by
          rw [Real.exp_le_exp]
          have key : (m : ℝ) * z.im ≥ m * c := by nlinarith
          nlinarith [Real.pi_pos, (Nat.cast_nonneg m : (0 : ℝ) ≤ m), z.im_pos]
        calc ‖a m‖ * rexp (-(2 * π) * (↑m + ↑n₀) * z.im)
            = ‖a m‖ * rexp (-(2 * π) * m * z.im) * rexp (-(2 * π) * n₀ * z.im) := by
              rw [hsplit]; ring
          _ ≤ ‖a m‖ * rexp (-(2 * π * c) * m) * rexp (-(2 * π) * n₀ * z.im) := by
              apply mul_le_mul_of_nonneg_right _ (le_of_lt (Real.exp_pos _))
              exact mul_le_mul_of_nonneg_left hexp_m (norm_nonneg _)
    _ = (∑' m, ‖a m‖ * rexp (-(2 * π * c) * m)) * rexp (-(2 * π) * n₀ * z.im) := tsum_mul_right
    _ = _ := by ring_nf

/--
If `F` has a Fourier expansion starting at index `n₀ > 0` with absolutely summable coefficients
at height `c > 0`, then `t^s * F(it) → 0` as `t → ∞` for any real power `s`.

This converts a Fourier expansion representation directly into polynomial decay on the
imaginary axis.
-/
theorem tendsto_rpow_mul_resToImagAxis_of_fourier_shift
    {F : ℍ → ℂ} {a : ℕ → ℂ} {n₀ : ℕ} {c : ℝ} (hn₀ : 0 < n₀) (hc : 0 < c)
    (hF : ∀ z : ℍ, F z =
      ∑' m : ℕ, a m * Complex.exp (2 * π * Complex.I * ((m + n₀ : ℕ) : ℂ) * (z : ℂ)))
    (ha : Summable (fun m : ℕ => ‖a m‖ * rexp (-(2 * π * c) * (m : ℝ)))) (s : ℝ) :
    Tendsto (fun t : ℝ => t ^ (s : ℂ) * F.resToImagAxis t) atTop (𝓝 0) :=
  tendsto_rpow_mul_resToImagAxis_of_isBigO_exp (by positivity)
    (isBigO_atImInfty_of_fourier_shift hn₀ hc hF ha) s

/-- Extract the imaginary part condition at a specific point from `ResToImagAxis.Real`. -/
lemma ResToImagAxis.Real.im_eq_zero_at {F : ℍ → ℂ} (hF : ResToImagAxis.Real F)
    {t : ℝ} (ht : 0 < t) (z : ℍ) (hz : z = ⟨Complex.I * t, by simp [ht]⟩) :
    (F z).im = 0 := by
  subst hz; simpa [Function.resToImagAxis, ResToImagAxis, ht] using hF t ht

/-- Extract the positivity condition at a specific point from `ResToImagAxis.Pos`. -/
lemma ResToImagAxis.Pos.re_pos_at {F : ℍ → ℂ} (hF : ResToImagAxis.Pos F)
    {t : ℝ} (ht : 0 < t) (z : ℍ) (hz : z = ⟨Complex.I * t, by simp [ht]⟩) :
    0 < (F z).re := by
  subst hz; simpa [Function.resToImagAxis, ResToImagAxis, ht] using hF.2 t ht

/-- Tendsto conversion: if F tends to c at atImInfty, then F.resToImagAxis tends to c at atTop. -/
lemma tendsto_resToImagAxis_of_tendsto_atImInfty {F : ℍ → ℂ} {c : ℂ}
    (hF : Tendsto F atImInfty (nhds c)) :
    Tendsto F.resToImagAxis atTop (nhds c) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Get eventual proximity from hF
  have hF_met : ∀ᶠ z in atImInfty, dist (F z) c < ε := Metric.tendsto_nhds.mp hF ε hε
  obtain ⟨A, hA⟩ := Filter.eventually_atImInfty.mp hF_met
  use max A 1
  intro t ht
  have ht_pos : 0 < t := lt_of_lt_of_le one_pos (le_of_max_le_right ht)
  simp only [Function.resToImagAxis, ResToImagAxis, ht_pos, ↓reduceDIte]
  set z : ℍ := ⟨Complex.I * t, by simp [ht_pos]⟩
  have hz_im : z.im = t := by simp [UpperHalfPlane.im, z]
  exact hA z (by simpa [hz_im] using le_of_max_le_left ht)
