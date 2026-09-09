/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.InnerProductSpace.LaxMilgram
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Tactic.Abel
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Analysis.Distribution.Sobolev
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Tactic.Linarith
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Tactic.Module
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.ODE.PicardLindelof
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.VectorCalculus

@[expose] public section

noncomputable section

namespace EulerGevreyCutoff

open Set Filter Complex MeasureTheory
open scoped Topology ContDiff

/-- Holomorphic function used to estimate the flat real bump by Cauchy's inequality. -/
def complexFlat (z : ℂ) : ℂ := Complex.exp (-z⁻¹)

theorem real_part_inv_lower_bound (x : ℝ) (hx : 0 < x) (z : ℂ)
    (hz : ‖z - (x : ℂ)‖ ≤ x / 2) : 1 / (8 * x) ≤ (z⁻¹).re := by
  have hre : x / 2 ≤ z.re := by
    have h := (Complex.abs_re_le_norm (z - (x : ℂ))).trans hz
    simp only [sub_re, ofReal_re] at h
    have := (abs_le.mp h).1
    linarith
  have hn : ‖z‖ ≤ 2 * x := by
    calc
      ‖z‖ = ‖(z - (x : ℂ)) + (x : ℂ)‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - (x : ℂ)‖ + ‖(x : ℂ)‖ := norm_add_le _ _
      _ ≤ x / 2 + x := by simpa [Complex.norm_real, abs_of_pos hx] using add_le_add_right hz x
      _ ≤ 2 * x := by linarith
  have hzn : z ≠ 0 := by intro h; simp [h] at hre; linarith
  have hden : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hzn)
  rw [Complex.inv_re, Complex.normSq_eq_norm_sq]
  apply (div_le_div_iff₀ (by positivity : 0 < 8 * x) hden).2
  have hsq : ‖z‖ ^ 2 ≤ (2 * x) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg z) hn 2
  nlinarith

theorem complexFlat_differentiableAt {z : ℂ} (hz : z ≠ 0) :
    DifferentiableAt ℂ complexFlat z :=
  Complex.differentiableAt_exp.comp z (differentiableAt_id.inv hz).neg

theorem complexFlat_disc_bound (x : ℝ) (hx : 0 < x) (z : ℂ)
    (hz : ‖z - (x : ℂ)‖ ≤ x / 2) :
    ‖complexFlat z‖ ≤ Real.exp (-(1 / (8 * x))) := by
  rw [complexFlat, Complex.norm_exp, neg_re]
  exact Real.exp_le_exp.mpr (neg_le_neg (real_part_inv_lower_bound x hx z hz))

theorem factorial_decay (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    t ^ n * Real.exp (-t) ≤ n.factorial := by
  have hf : 0 < (n.factorial : ℝ) := by positivity
  have hp := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp t ht n)
  calc
    t ^ n * Real.exp (-t) ≤ (Real.exp t * n.factorial) * Real.exp (-t) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = n.factorial := by rw [Real.exp_neg]; field_simp

theorem complexFlat_gevrey_bound (n : ℕ) (x : ℝ) (hx : 0 < x) :
    ‖iteratedDeriv n complexFlat (x : ℂ)‖ ≤ (16 : ℝ) ^ n * (n.factorial : ℝ) ^ 2 := by
  have hr : 0 < x / 2 := by positivity
  have hfd : DifferentiableOn ℂ complexFlat (Metric.closedBall (x : ℂ) (x / 2)) := by
    intro z hz
    have hd : ‖z - (x : ℂ)‖ ≤ x / 2 := by simpa [dist_eq_norm] using hz
    have hn : z ≠ 0 := by
      intro h
      simp [h, Complex.norm_real, abs_of_pos hx] at hd
      linarith
    exact (complexFlat_differentiableAt hn).differentiableWithinAt
  have hfc : DiffContOnCl ℂ complexFlat (Metric.ball (x : ℂ) (x / 2)) :=
    (hfd.mono Metric.closure_ball_subset_closedBall).diffContOnCl
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr hfc
    (fun z hz => complexFlat_disc_bound x hx z (by
      exact le_of_eq (by simpa only [Metric.mem_sphere, dist_eq_norm] using hz)))
  let t : ℝ := 1 / (8 * x)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hi : (x / 2)⁻¹ = 16 * t := by dsimp [t]; field_simp; ring
  have he : (n.factorial : ℝ) * Real.exp (-t) / (x / 2) ^ n =
      (16 : ℝ) ^ n * n.factorial * (t ^ n * Real.exp (-t)) := by
    rw [div_eq_mul_inv, ← inv_pow, hi, mul_pow]
    ring
  change ‖iteratedDeriv n complexFlat (x : ℂ)‖ ≤ _
  calc
    ‖iteratedDeriv n complexFlat (x : ℂ)‖ ≤
        n.factorial * Real.exp (-t) / (x / 2) ^ n := hc
    _ = (16 : ℝ) ^ n * n.factorial * (t ^ n * Real.exp (-t)) := he
    _ ≤ (16 : ℝ) ^ n * n.factorial * n.factorial :=
      mul_le_mul_of_nonneg_left (factorial_decay n t ht) (by positivity)
    _ = (16 : ℝ) ^ n * (n.factorial : ℝ) ^ 2 := by ring

theorem iteratedDeriv_real_restriction (f : ℂ → ℂ) (s : Set ℂ) (hs : IsOpen s)
    (hf : DifferentiableOn ℂ f s) (n : ℕ) (x : ℝ) (hx : (x : ℂ) ∈ s) :
    iteratedDeriv n (fun t : ℝ => (f (t : ℂ)).re) x =
      (iteratedDeriv n f (x : ℂ)).re := by
  have hc : ContDiffOn ℂ n f s := hf.contDiffOn hs
  have hr : ContDiffOn ℝ n f s := hc.restrict_scalars ℝ
  have hsR : IsOpen (Complex.ofRealCLM ⁻¹' s) := hs.preimage Complex.ofRealCLM.continuous
  have he := Complex.ofRealCLM.iteratedFDerivWithin_comp_right hr hs.uniqueDiffOn
    hsR.uniqueDiffOn hx (le_refl (n : ℕ∞ω))
  rw [iteratedFDerivWithin_of_isOpen n hsR hx] at he
  simp only [Complex.ofRealCLM_apply] at he
  rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) n hs hx] at he
  have hca : ContDiffAt ℂ n f (x : ℂ) := (hc _ hx).contDiffAt (hs.mem_nhds hx)
  have hra : ContDiffAt ℝ n (f ∘ Complex.ofRealCLM) x :=
    (hca.restrict_scalars ℝ).comp_continuousLinearMap Complex.ofRealCLM
  have hre := Complex.reCLM.iteratedFDeriv_comp_left hra (le_refl (n : ℕ∞ω))
  change (iteratedFDeriv ℝ n (Complex.reCLM ∘ (f ∘ Complex.ofRealCLM)) x)
    (fun _ => 1) = ((iteratedFDeriv ℂ n f (x : ℂ)) (fun _ => 1)).re
  rw [hre, he, ← hca.restrictScalars_iteratedFDeriv (𝕜 := ℝ)]
  simp

theorem polynomial_glue_flat (p : Polynomial ℝ) (n : ℕ) (x : ℝ) (hx : x ≤ 0) :
    iteratedDeriv n (fun y => p.eval y⁻¹ * expNegInvGlue y) x = 0 := by
  induction n generalizing p with
  | zero => simp [expNegInvGlue.zero_of_nonpos hx]
  | succ n ih =>
    rw [iteratedDeriv_succ']
    have hd : deriv (fun y => p.eval y⁻¹ * expNegInvGlue y) =
        fun y => (Polynomial.X ^ 2 * (p - p.derivative)).eval y⁻¹ * expNegInvGlue y :=
      funext (fun y => (expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul p y).deriv)
    rw [hd]
    exact ih _

theorem expNegInvGlue_gevrey_bound (n : ℕ) (x : ℝ) :
    |iteratedDeriv n expNegInvGlue x| ≤ (16 : ℝ) ^ n * (n.factorial : ℝ) ^ 2 := by
  by_cases hx : x ≤ 0
  · have hz : iteratedDeriv n expNegInvGlue x = 0 := by
      simpa using polynomial_glue_flat 1 n x hx
    rw [hz, abs_zero]
    positivity
  have hx : 0 < x := lt_of_not_ge hx
  have hs : IsOpen ({0}ᶜ : Set ℂ) := isClosed_singleton.isOpen_compl
  have hd : DifferentiableOn ℂ complexFlat ({0}ᶜ : Set ℂ) :=
    fun z hz => (complexFlat_differentiableAt hz).differentiableWithinAt
  have hr := iteratedDeriv_real_restriction complexFlat _ hs hd n x (by simpa using hx.ne')
  have hg : expNegInvGlue =ᶠ[nhds x] (fun t : ℝ => (complexFlat (t : ℂ)).re) := by
    filter_upwards [lt_mem_nhds hx] with y hy
    simp [expNegInvGlue, hy.not_ge, complexFlat, ← Complex.ofReal_inv,
      ← Complex.ofReal_neg, ← Complex.ofReal_exp]
  rw [hg.iteratedDeriv_eq n, hr]
  exact (Complex.abs_re_le_norm _).trans (complexFlat_gevrey_bound n x hx)

/-- Nonnegative even smooth bump supported on the unit interval. -/
def rawBump (x : ℝ) : ℝ := expNegInvGlue (x + 1) * expNegInvGlue (1 - x)

theorem rawBump_contDiff : ContDiff ℝ ∞ rawBump := by
  exact (expNegInvGlue.contDiff.comp (contDiff_id.add contDiff_const)).mul
    (expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id))

theorem rawBump_nonneg (x : ℝ) : 0 ≤ rawBump x :=
  mul_nonneg (expNegInvGlue.nonneg _) (expNegInvGlue.nonneg _)

theorem rawBump_even (x : ℝ) : rawBump (-x) = rawBump x := by
  simp only [rawBump, neg_add_eq_sub, sub_neg_eq_add]
  rw [add_comm (1 : ℝ) x, mul_comm]

theorem rawBump_pos_zero : 0 < rawBump 0 := by
  apply mul_pos <;> apply expNegInvGlue.pos_of_pos <;> norm_num

theorem rawBump_support : tsupport rawBump ⊆ Icc (-1 : ℝ) 1 := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  constructor
  · by_contra h
    have hz := expNegInvGlue.zero_of_nonpos (show x + 1 ≤ 0 by linarith)
    exact hx (by simp [rawBump, hz])
  · by_contra h
    have hz := expNegInvGlue.zero_of_nonpos (show 1 - x ≤ 0 by linarith)
    exact hx (by simp [rawBump, hz])

theorem rawBump_compactSupport : HasCompactSupport rawBump :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) rawBump_support

theorem rawBump_gevrey_bound (n : ℕ) (x : ℝ) :
    |iteratedDeriv n rawBump x| ≤ 3 * (16 : ℝ) ^ n * (n.factorial : ℝ) ^ 2 := by
  let f : ℝ → ℝ := fun y => expNegInvGlue (y + 1)
  let g : ℝ → ℝ := fun y => expNegInvGlue (1 - y)
  have hf : ContDiff ℝ ∞ f := expNegInvGlue.contDiff.comp (contDiff_id.add contDiff_const)
  have hg : ContDiff ℝ ∞ g := expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id)
  have hb₁ (k : ℕ) : |iteratedDeriv k f x| ≤ 1 * EulerGevrey.majorant 16 0 k := by
    simpa [f, EulerGevrey.majorant, iteratedDeriv_comp_add_const] using
      expNegInvGlue_gevrey_bound k (x + 1)
  have hb₂ (k : ℕ) : |iteratedDeriv k g x| ≤ 1 * EulerGevrey.majorant 16 0 k := by
    simpa [g, EulerGevrey.majorant, iteratedDeriv_comp_const_sub, abs_mul, abs_pow] using
      expNegInvGlue_gevrey_bound k (1 - x)
  have hp := EulerGevrey.sequence_product_majorant 16 1 1 (by norm_num) (by norm_num)
    (by norm_num) 0 0 (fun k => iteratedDeriv k f x) (fun k => iteratedDeriv k g x) hb₁ hb₂ n
  have hmul : rawBump = f * g := rfl
  rw [hmul, iteratedDeriv_mul (hf.contDiffAt.of_le (by simp)) (hg.contDiffAt.of_le (by simp))]
  simpa [EulerGevrey.majorant, mul_assoc] using hp

/-- Positive integral used to normalize the smooth transition. -/
def bumpMass : ℝ := ∫ t in (-1 : ℝ)..1, rawBump t

theorem bumpMass_pos : 0 < bumpMass := by
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    (rawBump_contDiff.continuous.intervalIntegrable _ _)
  · intro x hx
    apply mul_pos <;> apply expNegInvGlue.pos_of_pos <;> linarith [hx.1, hx.2]
  · norm_num

/-- Smooth monotone transition from zero to one, with explicit Gevrey bounds. -/
def transition (x : ℝ) : ℝ := (∫ t in (-1 : ℝ)..x, rawBump t) / bumpMass

theorem transition_hasDerivAt (x : ℝ) :
    HasDerivAt transition (rawBump x / bumpMass) x := by
  have hc := rawBump_contDiff.continuous
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).div_const bumpMass

theorem transition_deriv : deriv transition = fun x => rawBump x / bumpMass :=
  funext (fun x => (transition_hasDerivAt x).deriv)

theorem transition_contDiff : ContDiff ℝ ∞ transition := by
  rw [contDiff_infty_iff_deriv]
  exact ⟨fun x => (transition_hasDerivAt x).differentiableAt,
    transition_deriv ▸ rawBump_contDiff.div_const bumpMass⟩

theorem rawBump_eq_zero_of_le (x : ℝ) (hx : x ≤ -1) : rawBump x = 0 := by
  simp [rawBump, expNegInvGlue.zero_of_nonpos (show x + 1 ≤ 0 by linarith)]

theorem rawBump_eq_zero_of_ge (x : ℝ) (hx : 1 ≤ x) : rawBump x = 0 := by
  simp [rawBump, expNegInvGlue.zero_of_nonpos (show 1 - x ≤ 0 by linarith)]

theorem transition_zero_of_le (x : ℝ) (hx : x ≤ -1) : transition x = 0 := by
  have hi : (∫ t in x..(-1 : ℝ), rawBump t) = 0 := by
    calc
      _ = ∫ t in x..(-1 : ℝ), (0 : ℝ) := intervalIntegral.integral_congr (fun t ht =>
        rawBump_eq_zero_of_le t (((uIcc_of_le hx) ▸ ht).2))
      _ = 0 := by simp
  unfold transition
  rw [intervalIntegral.integral_symm, hi]
  simp

theorem transition_one_of_ge (x : ℝ) (hx : 1 ≤ x) : transition x = 1 := by
  have hi : (∫ t in (1 : ℝ)..x, rawBump t) = 0 := by
    calc
      _ = ∫ t in (1 : ℝ)..x, (0 : ℝ) := intervalIntegral.integral_congr (fun t ht =>
        rawBump_eq_zero_of_ge t (((uIcc_of_le hx) ▸ ht).1))
      _ = 0 := by simp
  unfold transition
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (rawBump_contDiff.continuous.intervalIntegrable (-1) 1)
    (rawBump_contDiff.continuous.intervalIntegrable 1 x), hi, add_zero]
  exact div_self bumpMass_pos.ne'

theorem transition_monotone : Monotone transition := by
  apply monotone_of_deriv_nonneg (fun x => (transition_hasDerivAt x).differentiableAt)
  intro x
  rw [transition_deriv]
  exact div_nonneg (rawBump_nonneg x) bumpMass_pos.le

theorem transition_mem_unitInterval (x : ℝ) : transition x ∈ Icc (0 : ℝ) 1 := by
  constructor
  · by_cases hx : x ≤ -1
    · rw [transition_zero_of_le x hx]
    · have h := transition_monotone (le_of_lt (lt_of_not_ge hx))
      rwa [transition_zero_of_le (-1) le_rfl] at h
  · by_cases hx : 1 ≤ x
    · rw [transition_one_of_ge x hx]
    · have h := transition_monotone (le_of_lt (lt_of_not_ge hx))
      rwa [transition_one_of_ge 1 le_rfl] at h

theorem transition_gevrey_bound (n : ℕ) (x : ℝ) :
    |iteratedDeriv n transition x| ≤
      (1 + 3 / bumpMass) * (16 : ℝ) ^ n * (n.factorial : ℝ) ^ 2 := by
  have hm := bumpMass_pos
  cases n with
  | zero =>
    simp only [iteratedDeriv_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, one_pow, mul_one]
    rw [abs_of_nonneg (transition_mem_unitInterval x).1]
    have h := (transition_mem_unitInterval x).2
    have : 0 < 3 / bumpMass := div_pos (by norm_num) bumpMass_pos
    linarith
  | succ n =>
    rw [iteratedDeriv_succ', transition_deriv]
    have he : (fun x => rawBump x / bumpMass) = fun x => rawBump x * bumpMass⁻¹ := by
      funext x
      rw [div_eq_mul_inv]
    rw [he, iteratedDeriv_mul_const_field, abs_mul, abs_inv, abs_of_pos bumpMass_pos]
    have hb := mul_le_mul_of_nonneg_right (rawBump_gevrey_bound n x) (inv_nonneg.mpr
      bumpMass_pos.le)
    have hp : (16 : ℝ) ^ n ≤ 16 ^ (n + 1) := by gcongr <;> norm_num
    have hf : (n.factorial : ℝ) ^ 2 ≤ ((n + 1).factorial : ℝ) ^ 2 := by
      gcongr
      omega
    have hA : 3 * bumpMass⁻¹ ≤ 1 + 3 / bumpMass := by rw [div_eq_mul_inv]; linarith
    calc
      _ ≤ (3 * 16 ^ n * (n.factorial : ℝ) ^ 2) * bumpMass⁻¹ := hb
      _ = (3 * bumpMass⁻¹) * 16 ^ n * (n.factorial : ℝ) ^ 2 := by ring
      _ ≤ (1 + 3 / bumpMass) * 16 ^ (n + 1) * ((n + 1).factorial : ℝ) ^ 2 := by
        gcongr


end EulerGevreyCutoff
