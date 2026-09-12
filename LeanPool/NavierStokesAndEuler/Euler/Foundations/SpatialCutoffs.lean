/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.Gevrey
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.SmoothLimit
import LeanPool.NavierStokesAndEuler.Euler.Foundations.GevreyFunctions
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Complex.Liouville

/-!
# Spatial Cutoffs
-/

section

/-!
# Gevrey Cutoff
-/

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

end
end

end

@[expose] public section

noncomputable section

namespace EulerSpatialCutoffs

open EulerGevrey EulerGevreyCutoff EulerGevreyFunctions EulerSmoothLimit
open scoped ContDiff
open Set

/-- The even one-dimensional bump normalized to have value one at the origin. -/
def normalizedBump (t : ℝ) : ℝ := rawBump t / rawBump 0

theorem normalizedBump_contDiff : ContDiff ℝ ∞ normalizedBump :=
  rawBump_contDiff.div_const _

theorem normalizedBump_zero : normalizedBump 0 = 1 :=
  div_self rawBump_pos_zero.ne'

theorem normalizedBump_even (t : ℝ) : normalizedBump (-t) = normalizedBump t := by
  simp only [normalizedBump, rawBump_even]

theorem normalizedBump_nonneg (t : ℝ) : 0 ≤ normalizedBump t :=
  div_nonneg (rawBump_nonneg t) rawBump_pos_zero.le

theorem normalizedBump_gevrey (n : ℕ) (t : ℝ) :
    |iteratedDeriv n normalizedBump t| ≤ (3 / rawBump 0) * majorant 16 0 n := by
  have he : normalizedBump = fun x => rawBump x * (rawBump 0)⁻¹ := by
    funext x
    simp [normalizedBump, div_eq_mul_inv]
  rw [he, iteratedDeriv_mul_const_field, abs_mul, abs_inv, abs_of_pos rawBump_pos_zero]
  have h := mul_le_mul_of_nonneg_right (rawBump_gevrey_bound n t)
    (inv_nonneg.mpr rawBump_pos_zero.le)
  simpa [majorant, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

/-- A plateau on the unit interval with support inside the interval of radius nine eighths. -/
def outerWindow (t : ℝ) : ℝ := transition (17 + 16 * t) * transition (17 - 16 * t)

theorem outerWindow_contDiff : ContDiff ℝ ∞ outerWindow :=
  (transition_contDiff.comp (contDiff_const.add (contDiff_const.mul contDiff_id))).mul
    (transition_contDiff.comp (contDiff_const.sub (contDiff_const.mul contDiff_id)))

theorem outerWindow_even (t : ℝ) : outerWindow (-t) = outerWindow t := by
  simp [outerWindow, sub_eq_add_neg, mul_comm]

theorem outerWindow_one (t : ℝ) (ht : |t| ≤ 1) : outerWindow t = 1 := by
  have ht' := abs_le.mp ht
  simp [outerWindow, transition_one_of_ge _ (show 1 ≤ 17 + 16 * t by linarith),
    transition_one_of_ge _ (show 1 ≤ 17 - 16 * t by linarith)]

theorem outerWindow_zero (t : ℝ) (ht : 9 / 8 ≤ |t|) : outerWindow t = 0 := by
  rcases le_abs.mp ht with h | h
  · simp [outerWindow, transition_zero_of_le _ (show 17 - 16 * t ≤ -1 by linarith)]
  · simp [outerWindow, transition_zero_of_le _ (show 17 + 16 * t ≤ -1 by linarith)]

theorem outerWindow_gevrey (n : ℕ) (t : ℝ) :
    |iteratedDeriv n outerWindow t| ≤
      (3 * (1 + 3 / bumpMass) ^ 2) * majorant 256 0 n := by
  let L : ℝ →L[ℝ] ℝ := (16 : ℝ) • ContinuousLinearMap.id ℝ ℝ
  have hn : ‖L‖ ≤ 16 := by
    apply L.opNorm_le_bound (by norm_num)
    intro y
    simp [L, norm_mul]
  have hmass := bumpMass_pos
  have hb : ∀ n t, |iteratedDeriv n transition t| ≤ (1 + 3 / bumpMass) * majorant 16 0 n :=
    fun n t => by simpa [majorant, mul_assoc] using transition_gevrey_bound n t
  have hp := affine_composition_bound transition transition_contDiff L 17 16
    (1 + 3 / bumpMass) 16 (by norm_num) (by positivity) (by norm_num) hn hb
  have hm := affine_composition_bound transition transition_contDiff (-L) 17 16
    (1 + 3 / bumpMass) 16 (by norm_num) (by positivity) (by norm_num)
    (by simpa using hn) hb
  have hf : ContDiff ℝ ∞ (fun y : ℝ => transition (L y + 17)) :=
    transition_contDiff.comp (L.contDiff.add contDiff_const)
  have hg : ContDiff ℝ ∞ (fun y : ℝ => transition ((-L) y + 17)) :=
    transition_contDiff.comp ((-L).contDiff.add contDiff_const)
  have h := product_bound _ _ hf hg 256 (1 + 3 / bumpMass) (1 + 3 / bumpMass)
    (by norm_num) (by positivity) (by positivity) (by norm_num at hp; exact hp)
    (by norm_num at hm; exact hm) n t
  have he : outerWindow = (fun y => transition (L y + 17) * transition ((-L) y + 17)) := by
    funext y
    simp [outerWindow, L, sub_eq_add_neg, add_comm]
  rw [he]
  simpa [L, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    Real.norm_eq_abs, sub_eq_add_neg, add_comm, pow_two, mul_assoc] using h

/-- Product of three copies of a scalar profile at a common coordinate scale. -/
def tensorCutoff (g : ℝ → ℝ) (a : ℝ) (x : Space) : ℝ := ∏ i : Fin 3, g (a * x i)

theorem tensorCutoff_contDiff (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (a : ℝ) :
    ContDiff ℝ ∞ (tensorCutoff g a) := by
  apply contDiff_prod
  intro i _
  have hc : ContDiff ℝ ∞ (fun y : Space => y i) :=
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff
  exact hg.comp (contDiff_const.mul hc)

theorem tensorCutoff_even (g : ℝ → ℝ) (hg : ∀ t, g (-t) = g t) (a : ℝ) (x : Space) :
    tensorCutoff g a (-x) = tensorCutoff g a x := by
  simp [tensorCutoff, hg]

theorem tensorCutoff_gevrey (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
    (a R A : ℝ) (ha : 0 ≤ a) (hR : 0 ≤ R) (hA : 0 ≤ A)
    (hb : ∀ n t, |iteratedDeriv n g t| ≤ A * majorant R 0 n)
    (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n (tensorCutoff g a) x‖ ≤ (3 * A) ^ 3 * majorant (R * a) 0 n := by
  have hL (i : Fin 3) : ‖(a • EuclideanSpace.proj i : Space →L[ℝ] ℝ)‖ ≤ a := by
    apply (a • EuclideanSpace.proj i : Space →L[ℝ] ℝ).opNorm_le_bound ha
    intro y
    simpa [Real.norm_eq_abs, abs_of_nonneg ha] using
      mul_le_mul_of_nonneg_left (PiLp.norm_apply_le y i) ha
  have hi (i : Fin 3) := linear_composition_bound g hg (a • EuclideanSpace.proj i)
    R A a hR hA ha (hL i) hb
  have h := finite_product_bound (Finset.univ : Finset (Fin 3))
    (fun i (y : Space) => g (a * y i))
    (fun i _ => hg.comp (contDiff_const.mul
      (show ContDiff ℝ ∞ (fun y : Space => y i) from
        (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff)))
    (R * a) A (mul_nonneg hR ha) hA (fun i _ k y => by
      simpa only [Function.comp_def, smul_apply, smul_eq_mul, PiLp.proj_apply] using hi i k y) n x
  have he : tensorCutoff g a = (fun y : Space => ∏ i : Fin 3, g (a * y i)) := rfl
  rw [he]
  simpa only [Finset.card_univ, Fintype.card_fin] using h

/-- Inner spatial cutoff used to localize the leading oscillatory packet. -/
def innerCutoff : Space → ℝ := tensorCutoff normalizedBump 4

/-- Outer plateau used by the compactly supported mean correction. -/
def outerCutoff : Space → ℝ := tensorCutoff outerWindow 1

theorem innerCutoff_contDiff : ContDiff ℝ ∞ innerCutoff :=
  tensorCutoff_contDiff _ normalizedBump_contDiff _

theorem outerCutoff_contDiff : ContDiff ℝ ∞ outerCutoff :=
  tensorCutoff_contDiff _ outerWindow_contDiff _

theorem innerCutoff_even (x : Space) : innerCutoff (-x) = innerCutoff x :=
  tensorCutoff_even _ normalizedBump_even _ _

theorem outerCutoff_even (x : Space) : outerCutoff (-x) = outerCutoff x :=
  tensorCutoff_even _ outerWindow_even _ _

theorem innerCutoff_nonneg (x : Space) : 0 ≤ innerCutoff x := by
  unfold innerCutoff tensorCutoff
  exact Finset.prod_nonneg (fun i _ => normalizedBump_nonneg _)

theorem innerCutoff_zero : innerCutoff 0 = 1 := by
  simp [innerCutoff, tensorCutoff, normalizedBump_zero]

theorem outerCutoff_one (x : Space) (hx : ‖x‖ ≤ 1) : outerCutoff x = 1 := by
  unfold outerCutoff tensorCutoff
  apply Finset.prod_eq_one
  intro i _
  apply outerWindow_one
  simpa only [one_mul, ← Real.norm_eq_abs] using (PiLp.norm_apply_le x i).trans hx

theorem innerCutoff_gevrey (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n innerCutoff x‖ ≤
      (9 / rawBump 0) ^ 3 * majorant 64 0 n := by
  have hpos := rawBump_pos_zero
  have h := tensorCutoff_gevrey _ normalizedBump_contDiff 4 16 (3 / rawBump 0)
    (by norm_num) (by norm_num) (by positivity) normalizedBump_gevrey n x
  simpa only [innerCutoff, show (16 : ℝ) * 4 = 64 by norm_num,
    show (3 : ℝ) * (3 / rawBump 0) = 9 / rawBump 0 by ring] using h

theorem outerCutoff_gevrey (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n outerCutoff x‖ ≤
      (9 * (1 + 3 / bumpMass) ^ 2) ^ 3 * majorant 256 0 n := by
  have h := tensorCutoff_gevrey _ outerWindow_contDiff 1 256 (3 * (1 + 3 / bumpMass) ^ 2)
    (by norm_num) (by norm_num) (by positivity) outerWindow_gevrey n x
  simpa only [outerCutoff, mul_one,
    show (3 : ℝ) * (3 * (1 + 3 / bumpMass) ^ 2) = 9 * (1 + 3 / bumpMass) ^ 2 by ring] using h

theorem cube_closed (r : ℝ) : IsClosed (({x : Space | ∀ i, |x i| ≤ r})) := by
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro i
  exact isClosed_le ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.abs) continuous_const

theorem norm_sq_le_of_mem_cube (r : ℝ) (hr : 0 ≤ r) (x : Space) (hx : x ∈ ({x : Space | ∀ i, |x i|
    ≤ r})) :
    ‖x‖ ^ 2 ≤ 3 * r ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    _ ≤ ∑ _i : Fin 3, r ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have h := (sq_le_sq₀ (abs_nonneg (x i)) hr).2 (hx i)
      simpa only [sq_abs] using h
    _ = _ := by simp

theorem tensorCutoff_support (g : ℝ → ℝ) (a b : ℝ) (ha : 0 < a)
    (hg : ∀ t, g t ≠ 0 → |t| ≤ b) :
    tsupport (tensorCutoff g a) ⊆ ({x : Space | ∀ i, |x i| ≤ b / a}) := by
  apply closure_minimal _ (cube_closed _)
  intro x hx i
  have hgx : g (a * x i) ≠ 0 := by
    exact (Finset.prod_ne_zero_iff.mp hx) i (Finset.mem_univ _)
  have h := hg (a * x i) hgx
  rw [abs_mul, abs_of_pos ha] at h
  exact (le_div_iff₀ ha).2 (by nlinarith)

theorem innerCutoff_support : tsupport innerCutoff ⊆ Metric.ball (0 : Space) (1 / 2) := by
  have hs := tensorCutoff_support normalizedBump 4 1 (by norm_num) (fun t ht => by
    have hraw : rawBump t ≠ 0 := fun h => ht (by simp [normalizedBump, h])
    exact abs_le.mpr (rawBump_support (subset_tsupport _ hraw)))
  intro x hx
  have hn := norm_sq_le_of_mem_cube (1 / 4) (by norm_num) x (hs hx)
  rw [Metric.mem_ball, dist_zero_right]
  nlinarith [norm_nonneg x]

theorem outerCutoff_support : tsupport outerCutoff ⊆ Metric.closedBall (0 : Space) 2 := by
  have hs := tensorCutoff_support outerWindow 1 (9 / 8) (by norm_num) (fun t ht => by
    by_contra h
    exact ht (outerWindow_zero t (le_of_lt (lt_of_not_ge h))))
  intro x hx
  have hc : x ∈ ({x : Space | ∀ i, |x i| ≤ 9 / 8}) := by simpa using hs hx
  have hn := norm_sq_le_of_mem_cube (9 / 8) (by norm_num) x hc
  rw [Metric.mem_closedBall, dist_zero_right]
  nlinarith [norm_nonneg x]

theorem innerCutoff_compactSupport : HasCompactSupport innerCutoff := by
  apply (isCompact_closedBall (0 : Space) (1 / 2)).of_isClosed_subset (isClosed_tsupport _)
  exact innerCutoff_support.trans Metric.ball_subset_closedBall

theorem outerCutoff_compactSupport : HasCompactSupport outerCutoff :=
  (isCompact_closedBall (0 : Space) 2).of_isClosed_subset (isClosed_tsupport _) outerCutoff_support

end EulerSpatialCutoffs
