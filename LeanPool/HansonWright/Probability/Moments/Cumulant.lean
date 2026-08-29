/-
Copyright (c) 2024 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto, Kazumi Kasaura, Naoto Onda, Yuma Mizuno, Sho Sonoda
-/
import Mathlib.Probability.Moments.Tilted
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Measure.Tilted

/-!
# Derivatives of Moment and Cumulant Generating Functions

Auxiliary results for differentiating exponential moments, tilted expectations, and cumulant
generating functions.

## Main definitions

This module extends Mathlib's existing moment-generating and tilted-measure definitions.

## Main results

* `ProbabilityTheory.tilt_first_deriv`: first derivative of an exponential moment.
* `ProbabilityTheory.tilt_second_deriv`: second derivative of an exponential moment.
* `ProbabilityTheory.cgf_deriv_one`: first derivative of the cumulant generating function.
* `ProbabilityTheory.cgf_deriv_two`: second derivative of the cumulant generating function.
-/

namespace LeanPool

open MeasureTheory Filter Finset Real
open _root_.ProbabilityTheory

noncomputable section

open scoped MeasureTheory ProbabilityTheory ENNReal NNReal

namespace ProbabilityTheory

variable {Ω ι : Type*} {m : MeasurableSpace Ω} {X : Ω → ℝ} {p : ℕ} {μ : Measure Ω}

section GeneratingFunctionDerivatives

lemma aemeasurable_expt {X : Ω → ℝ} (t : ℝ) (hX : AEMeasurable X μ) :
    AEStronglyMeasurable (fun ω ↦ rexp (t * (X ω))) μ :=
  aestronglyMeasurable_iff_aemeasurable.mpr <| measurable_exp.comp_aemeasurable' (hX.const_mul t)

lemma integrable_expt [IsFiniteMeasure μ] {X : Ω → ℝ} (t b : ℝ) (ht : t > 0)
    (hX : AEMeasurable X μ) (hb : ∀ᵐ ω ∂μ, X ω ≤ b) :
    Integrable (fun ω ↦ exp (t * (X ω))) μ := by
  have hm1 : HasFiniteIntegral (fun ω ↦ rexp (t * X ω)) μ := by
    have b' : ∀ᵐ ω ∂μ, rexp (t * X ω) ≤ rexp (t * b) := by
      filter_upwards [hb] with ω hb
      using exp_le_exp.mpr (mul_le_mul_of_nonneg_left hb (le_of_lt ht))
    have p : ∀ᵐ ω ∂μ, ‖rexp (t * X ω)‖₊ ≤ rexp (t * b) := by
      filter_upwards [b'] with ω b'
      rw [(by simp : ‖rexp (t * X ω)‖₊ = rexp (t * X ω))]
      exact b'
    have p'' : ∫⁻ ω, ‖rexp (t * X ω)‖₊ ∂μ ≤ ∫⁻ _, ‖rexp (t * b)‖₊ ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [p] with ω p
      simp only [ENNReal.coe_le_coe]
      rw [← (by simp : ‖rexp (t * b)‖₊ = rexp (t * b))] at p
      exact p
    suffices ∫⁻ _, ↑‖rexp (t * b)‖₊ ∂μ < ⊤ from lt_of_le_of_lt p'' this
    simp only [lintegral_const]
    apply ENNReal.mul_lt_top ENNReal.coe_lt_top (IsFiniteMeasure.measure_univ_lt_top)
  exact ⟨aestronglyMeasurable_iff_aemeasurable.mpr <|
    measurable_exp.comp_aemeasurable' (hX.const_mul t), hm1⟩

lemma integrable_expt_bound [IsFiniteMeasure μ] {X : Ω → ℝ} {t a b : ℝ} (hX : AEMeasurable X μ)
    (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    Integrable (fun ω ↦ exp (t * (X ω))) μ := by
  cases lt_trichotomy t 0 with
  | inr ht => cases ht with
    | inr ht => exact integrable_expt t b ht hX (h.mono fun ω h ↦ h.2)
    | inl ht => rw [ht]; simp only [zero_mul, exp_zero, integrable_const]
  | inl ht =>
    rw [(by ext ω; rw [(by ring : - t * (- X ω) = t * X ω)] :
      (fun ω ↦ rexp (t * X ω)) = (fun ω ↦ rexp (- t * (- X ω))))]
    apply integrable_expt (-t) _ _ hX.neg
    · filter_upwards [h] with ω h
      apply neg_le_neg h.1
    · exact Left.neg_pos_iff.mpr ht

lemma tilt_var_bound [IsProbabilityMeasure μ] (a b t : ℝ) {X : Ω → ℝ}
    (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b)
    (hX : AEMeasurable X μ) :
    variance X (μ.tilted (fun ω ↦ t * X ω)) ≤ ((b - a) / 2) ^ 2 := by
  have _ : IsProbabilityMeasure (μ.tilted fun ω ↦ t * X ω) :=
    isProbabilityMeasure_tilted (integrable_expt_bound hX h)
  exact variance_le_sq_of_bounded
      ((tilted_absolutelyContinuous μ fun ω ↦ t * X ω) h)
      (hX.mono_ac (tilted_absolutelyContinuous μ fun ω ↦ t * X ω))

theorem integrable_bounded [IsFiniteMeasure μ] (a b : ℝ)
    {X : Ω → ℝ} (hX : AEMeasurable X μ) (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    Integrable X μ := by
  have m1 : HasFiniteIntegral X μ := by
     apply (hasFiniteIntegral_const (max ‖a‖ ‖b‖)).mono'
     filter_upwards [h.mono fun ω h ↦ h.1, h.mono fun ω h ↦ h.2] with ω using abs_le_max_abs_abs
  exact ⟨aestronglyMeasurable_iff_aemeasurable.mpr hX, m1⟩

/-- Derivation of `mgf X μ t` is `μ[exp (t * X ω) * X ω]`.
In order to deal with the differentiation of parametric integrals,
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` are used in the proof. -/
theorem tilt_first_deriv [IsFiniteMeasure μ] (t a b : ℝ)
    {X : Ω → ℝ} (hX : AEMeasurable X μ) (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    let g := fun t ↦ mgf X μ t
    let g' := fun t ↦ μ[fun ω ↦ rexp (t * X ω) * X ω]
    Integrable (fun ω ↦ rexp (t * X ω) * X ω) μ → HasDerivAt g (g' t) t := by
  set c := max ‖a‖ ‖b‖
  set e := (fun t ↦ fun ω ↦ rexp (t * X ω))
  set e' := (fun t ↦ fun ω ↦ rexp (t * X ω) * X ω)
  suffices MeasureTheory.Integrable (e' t) μ ∧
    HasDerivAt (fun t ↦ μ[e t]) (μ[e' t]) t from by
    dsimp [mgf]
    intro hint
    apply this.2
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
  · change Metric.ball t (|t| + 1) ∈ nhds t
    refine Metric.ball_mem_nhds t ?_
    exact LE.le.trans_lt (abs_nonneg t) (lt_add_one |t|)
  · exact Filter.Eventually.of_forall
      (by intro t'; apply aemeasurable_expt _ hX : ∀ (x : ℝ), AEStronglyMeasurable (e x) μ)
  · simp only [e]; apply integrable_expt_bound hX h
  · simp only [e']
    apply AEMeasurable.aestronglyMeasurable;
    apply AEMeasurable.mul _ hX
    apply Measurable.comp_aemeasurable' _ _
    · exact measurable_exp
    · exact hX.const_mul t
  · set bound := fun ω ↦ rexp ((2 * |t| + 1) * |X ω|) * |X ω|
    apply ae_of_all μ
    change ∀ y, ∀ x ∈ Metric.ball t (|t| + 1), ‖e' x y‖ ≤ bound y
    intros y x b1
    calc
    _ = |rexp (x * X y)| * |X y| := abs_mul (rexp (x * X y)) (X y)
    _ = rexp (x * X y) * |X y| := by simp
    _ ≤ rexp (|x * X y|) * |X y| :=
      mul_le_mul_of_nonneg_right (exp_le_exp.mpr (le_abs_self (x * X y))) (abs_nonneg (X y))
    _ = rexp (|x| * |X y|) * |X y| := by
      rw [abs_mul x (X y)]
    _ ≤ rexp ((2 * |t| + 1) * |X y|) * |X y| := by
      have p2 : |x| ≤ 2 * |t| + 1 := by
        simp only [Metric.mem_ball] at b1
        linarith [le_trans' (le_of_lt b1) (abs_sub_abs_le_abs_sub x t)]
      exact mul_le_mul_of_nonneg_right
        (exp_le_exp.mpr (mul_le_mul_of_nonneg_right p2 (abs_nonneg (X y)))) (abs_nonneg (X y))
  · apply MeasureTheory.Integrable.bdd_mul
    · exact MeasureTheory.Integrable.abs (integrable_bounded a b hX h)
    · apply aemeasurable_expt (2 * |t| + 1) _
      apply Measurable.comp_aemeasurable' _ hX
      apply measurable_norm
    · filter_upwards [h] with ω h
      change ‖rexp ((2 * |t| + 1) * |X ω|)‖ ≤ rexp ((2 * |t| + 1) * |c|)
      simp only [norm_eq_abs, abs_exp, exp_le_exp]
      apply mul_le_mul_of_nonneg_left
        (le_trans' (le_abs_self (max ‖a‖ ‖b‖)) (abs_le_max_abs_abs h.1 h.2))
        (by linarith [abs_nonneg t] : 0 ≤ 2 * |t| + 1)
  suffices ∀ ω, ∀ x ∈ Metric.ball t (|t| + 1),
    HasDerivAt (fun x ↦ e x ω) (e' x ω) x from ae_of_all μ this
  intros ω x _
  exact HasDerivAt.exp (hasDerivAt_mul_const (X ω))

/-- Derivation of `μ[fun ω ↦ rexp (t * X ω) * X ω]` is `μ[fun ω ↦ rexp (t * X ω) * X ω ^ 2]`.
In order to deal with the differentiation of parametric integrals,
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` are used in the proof. -/
theorem tilt_second_deriv [IsFiniteMeasure μ] (t a b : ℝ)
    {X : Ω → ℝ} (hX : AEMeasurable X μ) (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    let g := fun t ↦ μ[fun ω ↦ rexp (t * X ω) * X ω]
    let g' := fun t ↦ μ[fun ω ↦ rexp (t * X ω) * X ω ^ 2]
    Integrable (fun ω ↦ rexp (t * X ω) * (X ω ^ 2)) μ → HasDerivAt g (g' t) t := by
  set c := max ‖a‖ ‖b‖
  set e := (fun t ↦ fun ω ↦ rexp (t * X ω) * X ω)
  set e' := (fun t ↦ fun ω ↦ rexp (t * X ω) * (X ω ^ 2))
  suffices MeasureTheory.Integrable (e' t) μ ∧
    HasDerivAt (fun t ↦ μ[e t]) (μ[e' t]) t from by
      intro _ _ hint
      apply this.2
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
  · change Metric.ball t (|t| + 1) ∈ nhds t
    refine Metric.ball_mem_nhds t ?_
    exact LE.le.trans_lt (abs_nonneg t) (lt_add_one |t|)
  · apply Filter.Eventually.of_forall
    intro t'
    dsimp only [e]
    rw [aestronglyMeasurable_iff_aemeasurable]
    apply AEMeasurable.mul _ hX
    exact Measurable.comp_aemeasurable' measurable_exp (hX.const_mul t')
  · simp only [e];
    apply MeasureTheory.Integrable.bdd_mul
      (integrable_bounded a b hX h) (aemeasurable_expt t hX)
    · filter_upwards [h] with ω h
      change ‖rexp (t * X ω)‖ ≤ rexp (|t| * c)
      simp only [norm_eq_abs, abs_exp, exp_le_exp]
      calc
      _ ≤ |t * X ω| := le_abs_self (t * X ω)
      _ = |t| * |X ω| := abs_mul t (X ω)
      _ ≤ |t| * c := by
        apply mul_le_mul_of_nonneg_left
        · rw [← (by dsimp only [c]; simp only
          [norm_eq_abs, abs_eq_self, le_max_iff, abs_nonneg, or_self] :
          |c| = c)]
          exact le_trans' (le_abs_self (max ‖a‖ ‖b‖)) (abs_le_max_abs_abs h.1 h.2)
        · exact abs_nonneg t
  · dsimp only [e']
    rw [aestronglyMeasurable_iff_aemeasurable]
    apply AEMeasurable.mul
    · apply Measurable.comp_aemeasurable' _ _
      · exact measurable_exp
      · exact hX.const_mul t
    exact hX.pow_const 2
  · set bound := fun ω ↦ rexp ((2 * |t| + 1) * |X ω|) * (|X ω| ^ 2)
    suffices ∀ ω, ∀ x ∈ Metric.ball t (|t| + 1), ‖e' x ω‖ ≤ bound ω from ae_of_all μ this
    intros ω x h
    dsimp [e', bound]
    simp only [sq_abs]
    show |rexp (x * X ω) * X ω ^ 2| ≤ rexp ((2 * |t| + 1) * |X ω|) * X ω ^ 2
    calc
    _ = |rexp (x * X ω)| * |(X ω ^ 2)| := abs_mul (rexp (x * X ω)) (X ω ^ 2)
    _ = rexp (x * X ω) * (X ω ^ 2) := by simp
    _ ≤ rexp ((2 * |t| + 1) * |X ω|) * X ω ^ 2 := by
      suffices rexp (x * X ω) ≤
        rexp ((2 * |t| + 1) * |X ω|) from mul_le_mul_of_nonneg_right this (sq_nonneg (X ω))
      simp only [exp_le_exp]
      calc
      _ ≤ |x * X ω| := le_abs_self (x * X ω)
      _ = |x| * |X ω| := abs_mul x (X ω)
      _ ≤ (2 * |t| + 1) * |X ω| := by
        suffices |x| ≤ 2 * |t| + 1 from mul_le_mul_of_nonneg_right this (abs_nonneg (X ω))
        simp only [Metric.mem_ball] at h
        linarith [le_trans' (le_of_lt h) (abs_sub_abs_le_abs_sub x t)]
  · apply MeasureTheory.Integrable.bdd_mul
    · simp only [sq_abs]
      rw [(by ext ω; ring : (fun ω ↦ X ω ^ 2) = (fun ω ↦ X ω * X ω))]
      apply MeasureTheory.Integrable.bdd_mul
        (integrable_bounded a b hX h) (aestronglyMeasurable_iff_aemeasurable.mpr hX)
      · filter_upwards [h] with x h
        simpa only [norm_eq_abs] using
          le_trans' (le_abs_self (max ‖a‖ ‖b‖)) (abs_le_max_abs_abs h.1 h.2)
    · apply aemeasurable_expt (2 * |t| + 1) _
      apply Measurable.comp_aemeasurable' _ hX
      apply measurable_norm
    · filter_upwards [h] with ω h
      change ‖rexp ((2 * |t| + 1) * |X ω|)‖ ≤ ‖rexp ((2 * |t| + 1) * c)‖
      simp only [norm_eq_abs, abs_exp, exp_le_exp]
      rw [← (abs_eq_self.mpr (le_trans' (le_max_left |a| ‖b‖) (abs_nonneg a)) : |c| = c)]
      exact mul_le_mul_of_nonneg_left
        (le_trans' (le_abs_self (max ‖a‖ ‖b‖)) (abs_le_max_abs_abs h.1 h.2))
        (by linarith [abs_nonneg t] : 0 ≤ 2 * |t| + 1)
  suffices ∀ ω, ∀ x ∈ Metric.ball t (|t| + 1),
    HasDerivAt (fun x ↦ e x ω) (e' x ω) x from ae_of_all μ this
  intros ω x _
  dsimp only [e, e']
  suffices HasDerivAt (fun x ↦ rexp (x * X ω)) (rexp (x * X ω) * X ω) x from by
    rw [(by ring : rexp (x * X ω) * X ω ^ 2 = (rexp (x * X ω) * X ω) * X ω)]
    exact HasDerivAt.mul_const this (X ω)
  exact HasDerivAt.exp (hasDerivAt_mul_const (X ω))

theorem integrable_deriv_expt [IsFiniteMeasure μ] (t a b : ℝ)
    {X : Ω → ℝ} (hX : AEMeasurable X μ) (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    Integrable (fun ω ↦ rexp (t * X ω) * X ω) μ := by
  apply MeasureTheory.Integrable.bdd_mul
    (integrable_bounded a b hX h) (aemeasurable_expt _ hX)
  · set c := max ‖a‖ ‖b‖
    filter_upwards [h] with ω h
    change ‖rexp (t * X ω)‖ ≤ ‖rexp (|t| * c)‖
    simp only [norm_eq_abs, abs_exp, exp_le_exp]
    rw [← (abs_eq_self.mpr (le_trans' (le_max_left |a| ‖b‖) (abs_nonneg a)) : |c| = c)]
    calc
    _ ≤ |t * X ω| := le_abs_self (t * X ω)
    _ = |t| * |X ω| := abs_mul t (X ω)
    _ ≤ |t| * |c| :=
      mul_le_mul_of_nonneg_left (le_trans' (le_abs_self (max ‖a‖ ‖b‖))
        (abs_le_max_abs_abs h.1 h.2) : |X ω| ≤ |c|) (abs_nonneg t)

theorem integral_tilted [IsFiniteMeasure μ]
    (t : ℝ) (f : ℝ → ℝ) {X : Ω → ℝ} (hX : AEMeasurable X μ) :
    (μ.tilted (fun ω ↦ t * X ω))[fun ω ↦ f (X ω)] =
    (μ[fun ω ↦ rexp (t * X ω) * f (X ω)]) / mgf X μ t := by
  calc
  _ = (∫ ω, ((∂Measure.tilted μ fun ω ↦ t * X ω/∂μ) ω).toReal • f (X ω) ∂μ) :=
    Eq.symm (MeasureTheory.integral_rnDeriv_smul (tilted_absolutelyContinuous μ fun ω ↦ t * X ω))
  _ = ∫ ω, (rexp (t * X ω) / μ[fun ω ↦ rexp (t * X ω)]) * f (X ω) ∂μ := by
    apply integral_congr_ae
    filter_upwards [rnDeriv_tilted_left_self (hX.const_mul t)] with ω w
    rw [w]
    simp only [smul_eq_mul, mul_eq_mul_right_iff, ENNReal.toReal_ofReal_eq_iff]
    left
    have q2 : 0 ≤ μ[fun ω ↦ rexp (t * X ω)] := by
      apply integral_nonneg
      apply Pi.le_def.mpr _
      intro i
      simp only [Pi.zero_apply]
      exact exp_nonneg (t * X i)
    exact div_nonneg (exp_nonneg (t * X ω)) q2
  _ = (∫ ω, (rexp (t * X ω) * f (X ω)) / (μ[fun ω ↦ rexp (t * X ω)]) ∂μ) := by
    refine integral_congr_ae (ae_of_all μ fun a ↦ ?_)
    simp only
    ring
  _ = (∫ ω, rexp (t * X ω) * f (X ω) ∂μ) / μ[fun ω ↦ rexp (t * X ω)] :=
    integral_div (μ[fun ω ↦ rexp (t * X ω)]) fun a ↦ rexp (t * X a) * f (X a)

/-! ### Derivatives of cumulant-/

/-- First derivative of cumulant `cgf X μ f`.
It can be described by exponential tilting. -/
theorem cgf_deriv_one [IsFiniteMeasure μ] [NeZero μ] (a b : ℝ)
    {X : Ω → ℝ} (hX : AEMeasurable X μ) (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    let f := fun t ↦ cgf X μ t
    let f' := fun t ↦ (μ.tilted (fun ω ↦ t * X ω))[X]
    ∀ x : ℝ, HasDerivAt f (f' x) x := by
  intros f f' t
  set g := fun t ↦ μ[fun ω ↦ rexp (t * X ω)]
  set g' := fun t ↦ μ[fun ω ↦ rexp (t * X ω) * X ω]
  dsimp [f']
  have r0 : ((μ.tilted (fun ω ↦ t * X ω))[fun ω ↦ id (X ω)]) =
    μ[fun ω ↦ rexp (t * X ω) * id (X ω)] / μ[fun ω ↦ rexp (t * X ω)] :=
    integral_tilted t id hX
  simp only [id_eq] at r0
  rw [r0]
  apply HasDerivAt.log
    (tilt_first_deriv _ _ _ hX h (integrable_deriv_expt t a b hX h))
    (mgf_pos' (NeZero.ne μ) (integrable_expt_bound hX h)).ne'

/-- Second derivative of cumulant `cgf X μ f`. -/
theorem cgf_deriv_two [IsFiniteMeasure μ] [NeZero μ] (a b : ℝ)
    {X : Ω → ℝ} (hX : AEMeasurable X μ) (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    let g' := fun t ↦ (μ.tilted (fun ω ↦ t * X ω))[X];
    let g'' := fun t ↦ (μ.tilted (fun ω ↦ t * X ω))[X ^ 2] - (μ.tilted (fun ω ↦ t * X ω))[X] ^ 2;
    ∀ x : ℝ, HasDerivAt g' (g'' x) x := by
  intro g' g'' t
  have r0 : (fun t ↦ ((μ.tilted (fun ω ↦ t * X ω))[fun ω ↦ id (X ω)])) =
    fun t ↦ μ[fun ω ↦ rexp (t * X ω) * id (X ω)] / μ[fun ω ↦ rexp (t * X ω)] := by
    ext t
    exact integral_tilted t id hX
  have r01 : (μ.tilted (fun ω ↦ t * X ω))[fun ω ↦ id (X ω)]  =
    μ[fun ω ↦ rexp (t * X ω) * id (X ω)] / μ[fun ω ↦ rexp (t * X ω)] :=
    integral_tilted t id hX
  have r0' : (μ.tilted (fun ω ↦ t * X ω))[fun ω ↦ (fun s ↦ s ^ 2) (X ω)] =
    μ[fun ω ↦ rexp (t * X ω) * (fun s ↦ s ^ 2) (X ω)] / μ[fun ω ↦ rexp (t * X ω)] :=
    integral_tilted t (fun x ↦ x ^ 2) hX
  simp only [id_eq] at r0 r0' r01
  dsimp [g', g'']
  rw [r0, r0', r01]
  have p : ((μ[fun ω ↦ rexp (t * X ω) * X ω ^ 2]) / μ[fun ω ↦ rexp (t * X ω)]) =
  ((μ[fun ω ↦ rexp (t * X ω) * X ω ^ 2]) * (μ[fun ω ↦ rexp (t * X ω)])) /
  ((μ[fun ω ↦ rexp (t * X ω)]) * (μ[fun ω ↦ rexp (t * X ω)])) := by
    apply Eq.symm (mul_div_mul_right (∫ ω, rexp (t * X ω) * X ω ^ 2 ∂μ)
    (μ[fun ω ↦ rexp (t * X ω)]) _)
    exact (mgf_pos' (NeZero.ne μ) (integrable_expt_bound hX h)).ne'
  rw [p, Eq.symm (pow_two (∫ ω, rexp (t * X ω) ∂μ))]
  have p'' : (((μ[fun ω ↦ rexp (t * X ω) * X ω ^ 2]) *
    (μ[fun ω ↦ rexp (t * X ω)])) / (μ[fun ω ↦ rexp (t * X ω)]) ^ 2 -
  (μ[fun ω ↦ rexp (t * X ω) * X ω]) ^ 2 / (μ[fun ω ↦ rexp (t * X ω)]) ^ 2) =
  ((μ[fun ω ↦ exp (t * (X ω)) * (X ω) ^ 2] *
    mgf X μ t) -
    (μ[fun ω ↦ exp (t * (X ω)) * X ω] * μ[fun ω ↦ exp (t * (X ω)) * X ω])) /
    (mgf X μ t ^ 2) := by
    rw [Eq.symm (pow_two (∫ ω, (fun ω ↦ rexp (t * X ω) * X ω) ω ∂μ))]
    exact
      div_sub_div_same ((μ[fun ω ↦ rexp (t * X ω) * X ω ^ 2]) * μ[fun ω ↦ rexp (t * X ω)])
        ((μ[fun ω ↦ rexp (t * X ω) * X ω]) ^ 2) ((μ[fun ω ↦ rexp (t * X ω)]) ^ 2)
  rw [div_pow, p'']
  apply HasDerivAt.div
  · set c := max ‖a‖ ‖b‖
    apply tilt_second_deriv _ _ _ hX h
    apply MeasureTheory.Integrable.bdd_mul (c := rexp (|t| * |c|))
    · rw [(by ext ω; ring : (fun ω ↦ X ω ^ 2) = (fun ω ↦ X ω * X ω))]
      apply MeasureTheory.Integrable.bdd_mul
        (integrable_bounded a b hX h) (aestronglyMeasurable_iff_aemeasurable.mpr hX)
      · filter_upwards [h] with x h
        simpa only [norm_eq_abs] using
          le_trans' (le_abs_self (max ‖a‖ ‖b‖)) (abs_le_max_abs_abs h.1 h.2)
    · exact aemeasurable_expt t hX
    · simp only [norm_eq_abs, abs_exp]
      filter_upwards [h] with ω h
      simp only [exp_le_exp]
      calc
      _ ≤ |t * X ω| := le_abs_self (t * X ω)
      _ = |t| * |X ω| := abs_mul t (X ω)
      _ ≤ |t| * |c| := mul_le_mul_of_nonneg_left (le_trans' (le_abs_self (max ‖a‖ ‖b‖))
                      (abs_le_max_abs_abs h.1 h.2)) (abs_nonneg t)
  · apply (tilt_first_deriv _ _ _ hX h)
          (integrable_deriv_expt t a b hX h)
  · exact (mgf_pos' (NeZero.ne μ) (integrable_expt_bound hX h)).ne'

end GeneratingFunctionDerivatives

end ProbabilityTheory

end

end LeanPool
