/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.Gevrey
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import LeanPool.NavierStokesAndEuler.Euler.Foundations.GevreyFunctions
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.InnerProductSpace.Basic
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Algebra.Order.Ring.Star

/-!
# Periodic Profile
-/

section

/-!
# Gevrey Inverse
-/

@[expose] public section

noncomputable section

namespace EulerGevreyInverse

open EulerGevrey Finset
open scoped ContDiff

theorem reciprocal_derivative_recurrence (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hnz : ∀ x, f x ≠ 0) (n : ℕ) (x : ℝ) :
    iteratedDeriv (n + 1) (fun y => (f y)⁻¹) x = -(f x)⁻¹ *
      ∑ k ∈ range (n + 1), ((n + 1).choose (k + 1) : ℝ) *
        iteratedDeriv (k + 1) f x * iteratedDeriv (n + 1 - (k + 1)) (fun y => (f y)⁻¹) x := by
  have hi : ContDiff ℝ ∞ (fun y => (f y)⁻¹) := hf.inv hnz
  have he : (fun y => f y * (f y)⁻¹) = fun _ => (1 : ℝ) := by
    funext y
    exact mul_inv_cancel₀ (hnz y)
  have hp := congrArg (fun g : ℝ → ℝ => iteratedDeriv (n + 1) g x) he
  have hmul : (fun y => f y * (f y)⁻¹) = f * (fun y => (f y)⁻¹) := rfl
  rw [hmul] at hp
  rw [iteratedDeriv_mul (hf.contDiffAt.of_le (by simp)) (hi.contDiffAt.of_le (by simp)),
    sum_range_succ'] at hp
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, iteratedDeriv_zero,
    Nat.sub_zero, iteratedDeriv_const, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
    ↓reduceIte] at hp
  have h := congrArg (fun z : ℝ => (f x)⁻¹ * z) hp
  field_simp [hnz x] at h ⊢
  linarith

theorem reciprocal_gevrey_shift (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hnz : ∀ x, f x ≠ 0) (A Rc R : ℝ) (hA : 1 ≤ A) (hRc : 0 ≤ Rc)
    (hR : 2 * A * (Rc + 1) ≤ R)
    (hb : ∀ x, |(f x)⁻¹| ≤ A)
    (hc : ∀ n x, |iteratedDeriv (n + 1) f x| ≤ majorant Rc 0 (n + 1))
    (n : ℕ) (x : ℝ) :
    |iteratedDeriv n (fun y => (f y)⁻¹) x| ≤ majorant R 1 n := by
  have hA0 : 0 ≤ A := by linarith
  have hR0 : 0 ≤ R := by nlinarith
  apply triangular_inverse_majorant A Rc R hA hRc hR 0
    (fun n => if n = 0 then 1 else 0)
    (fun n => |iteratedDeriv n (fun y => (f y)⁻¹) x|) _ _ n
  · intro k
    split_ifs with hk
    · subst k
      simp [majorant]
    · exact majorant_nonneg R hR0 0 k
  · intro k
    cases k with
    | zero => simpa using hb x
    | succ k =>
      rw [reciprocal_derivative_recurrence f hf hnz k x, abs_mul, abs_neg]
      simp only [Nat.succ_ne_zero, ↓reduceIte, zero_add]
      apply mul_le_mul (hb x) _ (abs_nonneg _) hA0
      calc
        _ ≤ ∑ j ∈ range (k + 1), |((k + 1).choose (j + 1) : ℝ) *
            iteratedDeriv (j + 1) f x *
            iteratedDeriv (k + 1 - (j + 1)) (fun y => (f y)⁻¹) x| := abs_sum_le_sum_abs _ _
        _ ≤ _ := by
          apply sum_le_sum
          intro j _
          have hj : (0 : ℝ) ≤ (k + 1).choose (j + 1) := by positivity
          have h := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hc j x) hj)
            (abs_nonneg (iteratedDeriv (k + 1 - (j + 1)) (fun y => (f y)⁻¹) x))
          simpa only [abs_mul, abs_of_nonneg hj, majorant, Nat.add_zero, mul_assoc] using h

theorem shift_one_bound (R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    majorant R 1 n ≤ R * majorant (4 * R) 0 n := by
  have hnat : n + 1 ≤ 2 ^ n := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [pow_succ]
      have : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
      omega
  have hn : (n : ℝ) + 1 ≤ (2 : ℝ) ^ n := by exact_mod_cast hnat
  have hs : ((n : ℝ) + 1) ^ 2 ≤ (4 : ℝ) ^ n := by
    calc
      _ ≤ ((2 : ℝ) ^ n) ^ 2 := by gcongr
      _ = _ := by rw [← pow_mul, mul_comm n 2, pow_mul]; norm_num
  simp only [majorant, Nat.add_zero, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, mul_pow, pow_succ]
  have hp := mul_le_mul_of_nonneg_right hs
    (mul_nonneg (pow_nonneg hR n) (mul_nonneg hR (sq_nonneg (n.factorial : ℝ))))
  linarith

theorem reciprocal_gevrey (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hnz : ∀ x, f x ≠ 0) (A Rc R : ℝ) (hA : 1 ≤ A) (hRc : 0 ≤ Rc)
    (hR : 2 * A * (Rc + 1) ≤ R)
    (hb : ∀ x, |(f x)⁻¹| ≤ A)
    (hc : ∀ n x, |iteratedDeriv (n + 1) f x| ≤ majorant Rc 0 (n + 1))
    (n : ℕ) (x : ℝ) :
    |iteratedDeriv n (fun y => (f y)⁻¹) x| ≤ R * majorant (4 * R) 0 n := by
  have hR0 : 0 ≤ R := by nlinarith
  exact (reciprocal_gevrey_shift f hf hnz A Rc R hA hRc hR hb hc n x).trans
    (shift_one_bound R hR0 n)

end EulerGevreyInverse

end
end

end

@[expose] public section

noncomputable section

namespace EulerPeriodicProfile

open scoped ContDiff
open Real
open EulerGevrey EulerGevreyInverse EulerGevreyFunctions

/-- Explicit smooth periodic profile with a narrow positive derivative peak. -/
def profile (δ t : ℝ) : ℝ := arctan (sin t / (1 + δ - cos t))

/-- Denominator of the derivative of the periodic profile. -/
def denominator (δ t : ℝ) : ℝ := (1 + δ) ^ 2 - 2 * (1 + δ) * cos t + 1

theorem first_denominator_pos (δ : ℝ) (hδ : 0 < δ) (t : ℝ) : 0 < 1 + δ - cos t := by
  linarith [cos_le_one t]

theorem denominator_lower (δ : ℝ) (hδ : 0 ≤ δ) (t : ℝ) : δ ^ 2 ≤ denominator δ t := by
  have h := mul_nonneg (show 0 ≤ 2 * (1 + δ) by positivity) (sub_nonneg.mpr (cos_le_one t))
  dsimp [denominator]
  linarith

theorem denominator_pos (δ : ℝ) (hδ : 0 < δ) (t : ℝ) : 0 < denominator δ t :=
  lt_of_lt_of_le (sq_pos_of_pos hδ) (denominator_lower δ hδ.le t)

theorem profile_contDiff (δ : ℝ) (hδ : 0 < δ) : ContDiff ℝ ∞ (profile δ) := by
  apply contDiff_arctan.comp
  exact contDiff_sin.div ((contDiff_const.add contDiff_const).sub contDiff_cos)
    (fun t => (first_denominator_pos δ hδ t).ne')

theorem profile_odd (δ t : ℝ) : profile δ (-t) = -profile δ t := by
  simp [profile, neg_div]

theorem profile_periodic (δ : ℝ) : Function.Periodic (profile δ) (2 * π) := by
  intro t
  simp [profile, sin_add_two_pi, cos_add_two_pi]

theorem profile_hasDerivAt (δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    HasDerivAt (profile δ) (((1 + δ) * cos t - 1) / denominator δ t) t := by
  have hd := first_denominator_pos δ hδ t
  have he := denominator_pos δ hδ t
  have hs := sin_sq_add_cos_sq t
  have hg : HasDerivAt (fun x => sin x / (1 + δ - cos x))
      ((cos t * (1 + δ - cos t) - sin t * sin t) / (1 + δ - cos t) ^ 2) t := by
    have hfun : (sin / ((fun _ : ℝ => 1 + δ) - cos)) =
        (fun x => sin x / (1 + δ - cos x)) := rfl
    have ht := (hasDerivAt_sin t).div
      ((hasDerivAt_const t (1 + δ)).sub (hasDerivAt_cos t)) hd.ne'
    rw [hfun] at ht
    simpa only [sub_neg_eq_add, zero_add, Pi.sub_apply, Pi.div_apply] using
      ht
  have heq : (1 + (sin t / (1 + δ - cos t)) ^ 2)⁻¹ *
      ((cos t * (1 + δ - cos t) - sin t * sin t) / (1 + δ - cos t) ^ 2) =
      ((1 + δ) * cos t - 1) / denominator δ t := by
    have hds : (1 + δ - cos t) ^ 2 + sin t ^ 2 = denominator δ t := by
      dsimp [denominator]
      linarith
    have hnum : cos t * (1 + δ - cos t) - sin t * sin t = (1 + δ) * cos t - 1 := by
      linarith
    rw [hnum]
    field_simp [hd.ne', he.ne']
    rw [hds]
    ring
  exact hg.arctan.congr_deriv (by simpa only [one_div] using heq)

theorem profile_deriv (δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    deriv (profile δ) t = ((1 + δ) * cos t - 1) / denominator δ t :=
  (profile_hasDerivAt δ hδ t).deriv

theorem profile_deriv_zero (δ : ℝ) (hδ : 0 < δ) : deriv (profile δ) 0 = δ⁻¹ := by
  rw [profile_deriv δ hδ]
  have he : denominator δ 0 = δ ^ 2 := by simp [denominator]; ring
  rw [he, cos_zero, mul_one]
  ring_nf
  field_simp [hδ.ne']

theorem profile_deriv_lower (δ : ℝ) (hδ : 0 < δ) (t : ℝ) : -1 ≤ deriv (profile δ) t := by
  rw [profile_deriv δ hδ, le_div_iff₀ (denominator_pos δ hδ t)]
  have h := mul_pos (show 0 < 1 + δ by linarith) (first_denominator_pos δ hδ t)
  dsimp [denominator]
  linarith

theorem profile_deriv_upper (δ : ℝ) (hδ : 0 < δ) (t : ℝ) : deriv (profile δ) t ≤ δ⁻¹ := by
  rw [profile_deriv δ hδ, inv_eq_one_div,
    div_le_div_iff₀ (denominator_pos δ hδ t) hδ]
  have h := mul_nonneg (mul_nonneg (show 0 ≤ 2 + δ by linarith)
    (show 0 ≤ 1 + δ by linarith)) (sub_nonneg.mpr (cos_le_one t))
  dsimp [denominator]
  linarith

theorem profile_mean_zero (δ : ℝ) : ∫ t in (-π)..π, profile δ t = 0 := by
  have he : (fun t => profile δ (-t)) = fun t => -profile δ t := funext (profile_odd δ)
  have hi := intervalIntegral.integral_comp_neg (f := profile δ) (a := -π) (b := π)
  rw [he, intervalIntegral.integral_neg] at hi
  simp only [neg_neg] at hi
  linarith

theorem denominator_contDiff (δ : ℝ) : ContDiff ℝ ∞ (denominator δ) := by
  exact ((contDiff_const.sub (contDiff_const.mul contDiff_cos)).add contDiff_const)

theorem denominator_derivative_bound (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (n : ℕ) (t : ℝ) : |iteratedDeriv (n + 1) (denominator δ) t| ≤ majorant 4 0 (n + 1) := by
  have he : denominator δ = fun t => ((1 + δ) ^ 2 + 1) - (2 * (1 + δ)) * cos t := by
    funext t
    dsimp [denominator]
    ring
  rw [he, iteratedDeriv_const_sub (by omega), iteratedDeriv_neg,
    iteratedDeriv_const_mul_field, abs_neg, abs_mul,
    abs_of_nonneg (show 0 ≤ 2 * (1 + δ) by positivity)]
  have hc := mul_le_mul_of_nonneg_left (abs_iteratedDeriv_cos_le_one (n + 1) t)
    (show 0 ≤ 2 * (1 + δ) by positivity)
  have hp : (4 : ℝ) ≤ 4 ^ (n + 1) := by
    have h : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
    rw [pow_succ]
    linarith
  have hf : (1 : ℝ) ≤ ((n + 1).factorial : ℝ) ^ 2 := by
    have hh : (1 : ℝ) ≤ (n + 1).factorial := by exact_mod_cast Nat.factorial_pos (n + 1)
    nlinarith
  dsimp [majorant]
  nlinarith

theorem denominator_inverse_bound (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (n : ℕ) (t : ℝ) :
    |iteratedDeriv n (fun t => (denominator δ t)⁻¹) t| ≤
      (10 * (δ ^ 2)⁻¹) * majorant (40 * (δ ^ 2)⁻¹) 0 n := by
  have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hA : 1 ≤ (δ ^ 2)⁻¹ := by
    apply (one_le_inv₀ hδsq).2
    nlinarith
  have hb (t : ℝ) : |(denominator δ t)⁻¹| ≤ (δ ^ 2)⁻¹ := by
    rw [abs_of_pos (inv_pos.mpr (denominator_pos δ hδ t))]
    exact inv_anti₀ hδsq (denominator_lower δ hδ.le t)
  have h := reciprocal_gevrey (denominator δ) (denominator_contDiff δ)
    (fun t => (denominator_pos δ hδ t).ne') ((δ ^ 2)⁻¹) 4 (10 * (δ ^ 2)⁻¹)
    hA (by norm_num) (by ring_nf; rfl) hb (denominator_derivative_bound δ hδ.le hδ1) n t
  simpa only [show (4 : ℝ) * (10 * (δ ^ 2)⁻¹) = 40 * (δ ^ 2)⁻¹ by ring] using h

/-- The numerator of the derivative of the explicit periodic profile. -/
def numerator (δ t : ℝ) : ℝ := (1 + δ) * cos t - 1

theorem numerator_contDiff (δ : ℝ) : ContDiff ℝ ∞ (numerator δ) :=
  (contDiff_const.mul contDiff_cos).sub contDiff_const

theorem numerator_derivative_bound (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (n : ℕ) (t : ℝ) : |iteratedDeriv n (numerator δ) t| ≤ 3 := by
  cases n with
  | zero =>
    simp only [iteratedDeriv_zero]
    dsimp [numerator]
    have ht := abs_cos_le_one t
    have h : |(1 + δ) * cos t - 1| ≤ |(1 + δ) * cos t| + |(1 : ℝ)| := abs_sub _ _
    rw [abs_mul, abs_of_nonneg (show 0 ≤ 1 + δ by positivity), abs_one] at h
    nlinarith
  | succ n =>
    have he : numerator δ = fun t => (-1 : ℝ) + (1 + δ) * cos t := by
      funext t
      dsimp [numerator]
      ring
    rw [he, iteratedDeriv_const_add (by omega), iteratedDeriv_const_mul_field,
      abs_mul, abs_of_nonneg (show 0 ≤ 1 + δ by positivity)]
    have h := mul_le_mul_of_nonneg_left (abs_iteratedDeriv_cos_le_one (n + 1) t)
      (show 0 ≤ 1 + δ by positivity)
    linarith

theorem profile_gevrey (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (n : ℕ) (t : ℝ) :
    |iteratedDeriv n (profile δ) t| ≤
      (100 * (δ ^ 2)⁻¹) * majorant (40 * (δ ^ 2)⁻¹) 0 n := by
  have hA : 1 ≤ (δ ^ 2)⁻¹ := by
    apply (one_le_inv₀ (sq_pos_of_pos hδ)).2
    nlinarith
  have hB : 1 ≤ 40 * (δ ^ 2)⁻¹ := by linarith
  have hBi : 0 ≤ 40 * (δ ^ 2)⁻¹ := by linarith
  have hAi : 0 ≤ (δ ^ 2)⁻¹ := by positivity
  cases n with
  | zero =>
    simp only [iteratedDeriv_zero, majorant, Nat.add_zero, pow_zero,
      Nat.factorial_zero, Nat.cast_one, one_pow, mul_one]
    have hp := arctan_lt_pi_div_two (sin t / (1 + δ - cos t))
    have hm := neg_pi_div_two_lt_arctan (sin t / (1 + δ - cos t))
    rw [abs_le]
    dsimp [profile]
    constructor <;> linarith [pi_le_four]
  | succ n =>
    have hn (k : ℕ) (x : ℝ) : ‖iteratedFDeriv ℝ k (numerator δ) x‖ ≤
        3 * majorant (40 * (δ ^ 2)⁻¹) 0 k := by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
      have hp : 1 ≤ (40 * (δ ^ 2)⁻¹) ^ k := one_le_pow₀ hB
      have hf : (1 : ℝ) ≤ (k.factorial : ℝ) ^ 2 := by
        have hh : (1 : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_pos k
        nlinarith
      have hb := numerator_derivative_bound δ hδ.le hδ1 k x
      dsimp [majorant]
      nlinarith
    have hi (k : ℕ) (x : ℝ) : ‖iteratedFDeriv ℝ k (fun t => (denominator δ t)⁻¹) x‖ ≤
        (10 * (δ ^ 2)⁻¹) * majorant (40 * (δ ^ 2)⁻¹) 0 k := by
      simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using
        denominator_inverse_bound δ hδ hδ1 k x
    have hp := product_bound (numerator δ) (fun t => (denominator δ t)⁻¹)
      (numerator_contDiff δ) ((denominator_contDiff δ).inv (fun t => (denominator_pos δ hδ t).ne'))
      (40 * (δ ^ 2)⁻¹) 3 (10 * (δ ^ 2)⁻¹) hBi (by norm_num) (by positivity) hn hi n t
    have he : deriv (profile δ) = fun t => numerator δ t * (denominator δ t)⁻¹ := by
      funext t
      rw [profile_deriv δ hδ]
      rfl
    rw [iteratedDeriv_succ', he]
    have hm : majorant (40 * (δ ^ 2)⁻¹) 0 n ≤ majorant (40 * (δ ^ 2)⁻¹) 0 (n + 1) := by
      unfold majorant
      apply mul_le_mul
      · exact pow_le_pow_right₀ hB (by omega)
      · gcongr; omega
      · positivity
      · positivity
    have hp' : |iteratedDeriv n (fun t => numerator δ t * (denominator δ t)⁻¹) t| ≤
        (90 * (δ ^ 2)⁻¹) * majorant (40 * (δ ^ 2)⁻¹) 0 n := by
      simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
        show (3 : ℝ) * 3 * (10 * (δ ^ 2)⁻¹) = 90 * (δ ^ 2)⁻¹ by ring] using hp
    exact hp'.trans (mul_le_mul (by linarith) hm (majorant_nonneg _ hBi _ _)
      (by positivity))

end EulerPeriodicProfile
