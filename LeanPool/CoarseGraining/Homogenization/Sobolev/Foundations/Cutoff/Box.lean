/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Ambient.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-! # Box -/

namespace Homogenization

open Real Polynomial MeasureTheory
open scoped BigOperators

/-!
# Smooth box cutoffs

For a closed axis box `B = ∏ᵢ [loᵢ, hiᵢ]` (`lo ≤ hi` componentwise) and a margin
`ℓ > 0`, this file constructs a smooth cutoff `η : Vec d → ℝ`
(`Vec d = Fin d → ℝ`) that is `1` on `B`, `0` off the ℓ-enlargement
`∏ᵢ [loᵢ − ℓ, hiᵢ + ℓ]`, valued in `[0, 1]`, with coordinate partial derivatives
bounded by `16 / ℓ`.

The construction is the coordinatewise product `η(x) = ∏ᵢ ψᵢ(xᵢ)` of the
one-dimensional plateau profiles `ψᵢ = profile (loᵢ) (hiᵢ) ℓ`, each built from
`Real.smoothTransition`.  The development has three layers:

* an explicit derivative bound `|smoothTransition'| ≤ 8`, proved by elementary
  calculus on the building block `expNegInvGlue`;
* the one-dimensional plateau `profile lo hi ℓ`, equal to `1` on `[lo, hi]`, `0`
  off `[lo − ℓ, hi + ℓ]`, with derivative bounded by `16 / ℓ`;
* the `d`-dimensional product cutoff `boxCutoff`, bundled as `SmoothBoxCutoff`,
  with the coordinate derivative bound, squared-gradient bound, and
  support-volume bound (`exists_smoothBoxCutoff`).

Partial derivatives are exposed as `fderiv ℝ η x (Pi.single i 1)`, matching the
ambient `HasWeakPartialDerivOn` pairing.  The explicit gradient constant is
`C = 16`.
-/

/-- `expNegInvGlue` never exceeds `1`. -/
theorem expNegInvGlue_le_one (x : ℝ) : expNegInvGlue x ≤ 1 := by
  unfold expNegInvGlue
  split_ifs with hx
  · exact zero_le_one
  · rw [Real.exp_le_one_iff]
    have hx' : 0 < x := lt_of_not_ge hx
    simp only [neg_nonpos, inv_nonneg]
    exact hx'.le

/-- The derivative of `expNegInvGlue` at `x` equals `x⁻² · expNegInvGlue x`
(interpreting `0⁻¹ = 0`, so both sides vanish for `x ≤ 0`). -/
theorem expNegInvGlue_hasDerivAt (x : ℝ) :
    HasDerivAt expNegInvGlue (x⁻¹ ^ 2 * expNegInvGlue x) x := by
  have h := expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : ℝ[X]) x
  simp only [Polynomial.derivative_one, sub_zero, mul_one, Polynomial.eval_one, one_mul,
    Polynomial.eval_pow, Polynomial.eval_X] at h
  exact h

/-- One-variable calculus fact: `s · e^{-s} ≤ e^{-1}` for every real `s`
(equality at `s = 1`). -/
theorem mul_exp_neg_le (s : ℝ) : s * Real.exp (-s) ≤ Real.exp (-1) := by
  have hle : s ≤ Real.exp (s - 1) := by
    have := Real.add_one_le_exp (s - 1)
    linarith
  calc s * Real.exp (-s) ≤ Real.exp (s - 1) * Real.exp (-s) :=
        mul_le_mul_of_nonneg_right hle (Real.exp_nonneg _)
    _ = Real.exp (-1) := by rw [← Real.exp_add]; ring_nf

/-- Derivative maximum for the building block:
`x⁻² · expNegInvGlue x ≤ 4 e⁻²` for every `x`.  The sharp value `4 e⁻²` is
attained at `x = 1/2`. -/
theorem expNegInvGlue_deriv_le (x : ℝ) :
    x⁻¹ ^ 2 * expNegInvGlue x ≤ 4 * Real.exp (-2) := by
  rcases le_or_gt x 0 with hx | hx
  · rw [expNegInvGlue.zero_of_nonpos hx, mul_zero]
    positivity
  · -- For `x > 0`, `expNegInvGlue x = exp (-x⁻¹)`; set `t = x⁻¹ > 0`, `s = t/2`.
    have hgx : expNegInvGlue x = Real.exp (-x⁻¹) := by
      simp [expNegInvGlue, not_le.2 hx]
    rw [hgx]
    set t := x⁻¹ with ht
    -- `t² · exp (-t) = 4 · a²` where `a = (t/2) · exp (-t/2) ≤ exp (-1)`, `0 ≤ a`.
    have ht0 : 0 < t := inv_pos.2 hx
    set a := (t / 2) * Real.exp (-(t / 2)) with ha
    have ha0 : 0 ≤ a := by positivity
    have hale : a ≤ Real.exp (-1) := mul_exp_neg_le (t / 2)
    have hsq : a * a ≤ Real.exp (-1) * Real.exp (-1) := mul_self_le_mul_self ha0 hale
    have e2 : Real.exp (-(t / 2)) * Real.exp (-(t / 2)) = Real.exp (-t) := by
      rw [← Real.exp_add]; ring_nf
    have haa : a * a = (t ^ 2 * Real.exp (-t)) / 4 := by
      rw [ha, mul_mul_mul_comm, e2]; ring
    have hee : Real.exp (-1) * Real.exp (-1) = Real.exp (-2) := by
      rw [← Real.exp_add]; ring_nf
    rw [hee, haa] at hsq
    linarith

/-- On `[1/2, ∞)` the building block is bounded below by `e⁻²`. -/
theorem expNegInvGlue_ge_of_half_le {y : ℝ} (hy : 1 / 2 ≤ y) :
    Real.exp (-2) ≤ expNegInvGlue y := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hgy : expNegInvGlue y = Real.exp (-y⁻¹) := by
    simp [expNegInvGlue, not_le.2 hy0]
  rw [hgy]
  apply Real.exp_le_exp.2
  have hmul : y⁻¹ * y = 1 := inv_mul_cancel₀ hy0.ne'
  have hinv : y⁻¹ ≤ 2 := by
    nlinarith [mul_nonneg (inv_pos.2 hy0).le (show (0:ℝ) ≤ y - 1 / 2 by linarith), hmul]
  linarith

/-- Denominator lower bound for `smoothTransition`: since one of `x`, `1 - x`
is `≥ 1/2`, we have `e⁻² ≤ g x + g(1 - x)`. -/
theorem denom_ge (x : ℝ) :
    Real.exp (-2) ≤ expNegInvGlue x + expNegInvGlue (1 - x) := by
  rcases le_total (1 / 2 : ℝ) x with hx | hx
  · have := expNegInvGlue_ge_of_half_le hx
    have hb := expNegInvGlue.nonneg (1 - x)
    linarith
  · have hx' : (1 / 2 : ℝ) ≤ 1 - x := by linarith
    have := expNegInvGlue_ge_of_half_le hx'
    have ha := expNegInvGlue.nonneg x
    linarith

/-- Explicit derivative of `Real.smoothTransition`, in the form
`(g'(x) g(1-x) + g(x) g'(1-x)) / (g(x) + g(1-x))²` with both numerator
summands manifestly nonnegative. -/
theorem smoothTransition_hasDerivAt (x : ℝ) :
    HasDerivAt Real.smoothTransition
      ((x⁻¹ ^ 2 * expNegInvGlue x * expNegInvGlue (1 - x)
        + expNegInvGlue x * ((1 - x)⁻¹ ^ 2 * expNegInvGlue (1 - x)))
        / (expNegInvGlue x + expNegInvGlue (1 - x)) ^ 2) x := by
  have ha := expNegInvGlue_hasDerivAt x
  have hb := (expNegInvGlue_hasDerivAt (1 - x)).comp x ((hasDerivAt_id x).const_sub 1)
  have hD := ha.add hb
  have hDne : expNegInvGlue x + expNegInvGlue (1 - x) ≠ 0 :=
    (Real.smoothTransition.pos_denom x).ne'
  have hq := ha.div hD hDne
  simp only [Pi.add_apply, Function.comp_apply] at hq
  convert hq using 1
  all_goals first
    | rfl
    | ring

/-- **Explicit derivative bound for `Real.smoothTransition`.**  For every `x`,
`|smoothTransition'(x)| ≤ 8`.  (The sharp constant is `2`, at `x = 1/2`; `8`
is what the elementary route below delivers.) -/
theorem smoothTransition_deriv_abs_le (x : ℝ) :
    |deriv Real.smoothTransition x| ≤ 8 := by
  rw [(smoothTransition_hasDerivAt x).deriv]
  set a := expNegInvGlue x with ha_def
  set b := expNegInvGlue (1 - x) with hb_def
  set P := x⁻¹ ^ 2 * expNegInvGlue x with hP_def
  set Q := (1 - x)⁻¹ ^ 2 * expNegInvGlue (1 - x) with hQ_def
  have ha0 : 0 ≤ a := expNegInvGlue.nonneg x
  have hb0 : 0 ≤ b := expNegInvGlue.nonneg (1 - x)
  have hP0 : 0 ≤ P := by rw [hP_def]; positivity
  have hQ0 : 0 ≤ Q := by rw [hQ_def]; positivity
  have hPle : P ≤ 4 * Real.exp (-2) := expNegInvGlue_deriv_le x
  have hQle : Q ≤ 4 * Real.exp (-2) := expNegInvGlue_deriv_le (1 - x)
  have hab : Real.exp (-2) ≤ a + b := denom_ge x
  have hab0 : 0 < a + b := lt_of_lt_of_le (Real.exp_pos _) hab
  have hden : 0 < (a + b) ^ 2 := by positivity
  have hval0 : 0 ≤ (P * b + a * Q) / (a + b) ^ 2 := by positivity
  rw [abs_of_nonneg hval0, div_le_iff₀ hden]
  -- `P b + a Q ≤ (P + Q)(a + b) ≤ 8 e⁻² (a + b) ≤ 8 (a + b)²`.
  have step1 : P * b + a * Q ≤ (P + Q) * (a + b) := by
    nlinarith [mul_nonneg hP0 ha0, mul_nonneg hQ0 hb0]
  have step2 : (P + Q) * (a + b) ≤ 8 * Real.exp (-2) * (a + b) := by
    nlinarith [hab0, hPle, hQle]
  have step3 : 8 * Real.exp (-2) * (a + b) ≤ 8 * (a + b) ^ 2 := by
    nlinarith [hab, hab0]
  linarith

/-- One-dimensional smooth plateau profile: `1` on `[lo, hi]`, `0` off
`[lo - ℓ, hi + ℓ]`, valued in `[0, 1]`. -/
noncomputable def profile (lo hi ℓ : ℝ) (t : ℝ) : ℝ :=
  Real.smoothTransition ((t - (lo - ℓ)) / ℓ) * Real.smoothTransition (((hi + ℓ) - t) / ℓ)

variable {lo hi ℓ : ℝ}

theorem profile_nonneg (t : ℝ) : 0 ≤ profile lo hi ℓ t :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem profile_le_one (t : ℝ) : profile lo hi ℓ t ≤ 1 := by
  have h := mul_le_mul (Real.smoothTransition.le_one ((t - (lo - ℓ)) / ℓ))
    (Real.smoothTransition.le_one (((hi + ℓ) - t) / ℓ))
    (Real.smoothTransition.nonneg _) (zero_le_one)
  rw [mul_one] at h
  exact h

theorem profile_abs_le_one (t : ℝ) : |profile lo hi ℓ t| ≤ 1 := by
  rw [abs_of_nonneg (profile_nonneg t)]; exact profile_le_one t

theorem profile_contDiff : ContDiff ℝ (⊤ : ℕ∞) (profile lo hi ℓ) := by
  unfold profile
  fun_prop

theorem profile_differentiable : Differentiable ℝ (profile lo hi ℓ) :=
  profile_contDiff.differentiable (by simp)

/-- The profile is identically `1` on the core interval `[lo, hi]`. -/
theorem profile_eq_one (hℓ : 0 < ℓ) {t : ℝ} (hlo : lo ≤ t) (hhi : t ≤ hi) :
    profile lo hi ℓ t = 1 := by
  have hL : Real.smoothTransition ((t - (lo - ℓ)) / ℓ) = 1 := by
    apply Real.smoothTransition.one_of_one_le
    rw [one_le_div hℓ]; linarith
  have hR : Real.smoothTransition (((hi + ℓ) - t) / ℓ) = 1 := by
    apply Real.smoothTransition.one_of_one_le
    rw [one_le_div hℓ]; linarith
  rw [profile, hL, hR, mul_one]

/-- The profile vanishes to the left of the enlarged interval. -/
theorem profile_eq_zero_left (hℓ : 0 < ℓ) {t : ℝ} (ht : t ≤ lo - ℓ) :
    profile lo hi ℓ t = 0 := by
  have hL : Real.smoothTransition ((t - (lo - ℓ)) / ℓ) = 0 := by
    apply Real.smoothTransition.zero_of_nonpos
    rw [div_le_iff₀ hℓ]; linarith
  rw [profile, hL, zero_mul]

/-- The profile vanishes to the right of the enlarged interval. -/
theorem profile_eq_zero_right (hℓ : 0 < ℓ) {t : ℝ} (ht : hi + ℓ ≤ t) :
    profile lo hi ℓ t = 0 := by
  have hR : Real.smoothTransition (((hi + ℓ) - t) / ℓ) = 0 := by
    apply Real.smoothTransition.zero_of_nonpos
    rw [div_le_iff₀ hℓ]; linarith
  rw [profile, hR, mul_zero]

/-- Off the enlarged interval `[lo - ℓ, hi + ℓ]` the profile is `0`. -/
theorem profile_eq_zero_of_notMem (hℓ : 0 < ℓ) {t : ℝ}
    (ht : t ∉ Set.Icc (lo - ℓ) (hi + ℓ)) : profile lo hi ℓ t = 0 := by
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
  rcases ht with ht | ht
  · exact profile_eq_zero_left hℓ ht.le
  · exact profile_eq_zero_right hℓ ht.le

/-- **Derivative bound for the 1-d profile:** `|profile'(t)| ≤ 16 / ℓ`. -/
theorem profile_deriv_abs_le (hℓ : 0 < ℓ) (t : ℝ) :
    |deriv (profile lo hi ℓ) t| ≤ 16 / ℓ := by
  -- affine inner maps and their derivatives
  have hArgL : HasDerivAt (fun t => (t - (lo - ℓ)) / ℓ) (1 / ℓ) t :=
    ((hasDerivAt_id t).sub_const (lo - ℓ)).div_const ℓ
  have hArgR : HasDerivAt (fun t => ((hi + ℓ) - t) / ℓ) (-1 / ℓ) t := by
    have h := (((hasDerivAt_id t).const_sub (hi + ℓ)).div_const ℓ)
    simpa using h
  -- the two transition factors
  have hst : ∀ s : ℝ, HasDerivAt Real.smoothTransition (deriv Real.smoothTransition s) s :=
    fun s => (Real.smoothTransition.contDiff.differentiable_one s).hasDerivAt
  have hL := (hst ((t - (lo - ℓ)) / ℓ)).comp t hArgL
  have hR := (hst (((hi + ℓ) - t) / ℓ)).comp t hArgR
  have hd : HasDerivAt (profile lo hi ℓ)
      (deriv Real.smoothTransition ((t - (lo - ℓ)) / ℓ) * (1 / ℓ)
          * Real.smoothTransition (((hi + ℓ) - t) / ℓ)
        + Real.smoothTransition ((t - (lo - ℓ)) / ℓ)
          * (deriv Real.smoothTransition (((hi + ℓ) - t) / ℓ) * (-1 / ℓ))) t :=
    hL.mul hR
  rw [hd.deriv]
  -- abs bounds on each ingredient
  have h8L : |deriv Real.smoothTransition ((t - (lo - ℓ)) / ℓ)| ≤ 8 :=
    smoothTransition_deriv_abs_le _
  have h8R : |deriv Real.smoothTransition (((hi + ℓ) - t) / ℓ)| ≤ 8 :=
    smoothTransition_deriv_abs_le _
  have h1L : |Real.smoothTransition ((t - (lo - ℓ)) / ℓ)| ≤ 1 := by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]; exact Real.smoothTransition.le_one _
  have h1R : |Real.smoothTransition (((hi + ℓ) - t) / ℓ)| ≤ 1 := by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]; exact Real.smoothTransition.le_one _
  have hℓ0 : (0 : ℝ) ≤ 1 / ℓ := (div_pos one_pos hℓ).le
  have hinv : |1 / ℓ| = 1 / ℓ := abs_of_pos (div_pos one_pos hℓ)
  have hinv' : |(-1 : ℝ) / ℓ| = 1 / ℓ := by
    rw [abs_div, abs_neg, abs_one, abs_of_pos hℓ]
  have t1 : |deriv Real.smoothTransition ((t - (lo - ℓ)) / ℓ) * (1 / ℓ)
        * Real.smoothTransition (((hi + ℓ) - t) / ℓ)| ≤ 8 / ℓ := by
    rw [abs_mul, abs_mul, hinv, mul_right_comm]
    have h := mul_le_mul h8L h1R (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    calc |deriv Real.smoothTransition ((t - (lo - ℓ)) / ℓ)|
          * |Real.smoothTransition (((hi + ℓ) - t) / ℓ)| * (1 / ℓ)
        ≤ 8 * 1 * (1 / ℓ) := mul_le_mul_of_nonneg_right h hℓ0
      _ = 8 / ℓ := by ring
  have t2 : |Real.smoothTransition ((t - (lo - ℓ)) / ℓ)
        * (deriv Real.smoothTransition (((hi + ℓ) - t) / ℓ) * (-1 / ℓ))| ≤ 8 / ℓ := by
    rw [abs_mul, abs_mul, hinv']
    have hR' : |deriv Real.smoothTransition (((hi + ℓ) - t) / ℓ)| * (1 / ℓ) ≤ 8 * (1 / ℓ) :=
      mul_le_mul_of_nonneg_right h8R hℓ0
    calc |Real.smoothTransition ((t - (lo - ℓ)) / ℓ)|
          * (|deriv Real.smoothTransition (((hi + ℓ) - t) / ℓ)| * (1 / ℓ))
        ≤ 1 * (8 * (1 / ℓ)) :=
          mul_le_mul h1L hR' (mul_nonneg (abs_nonneg _) hℓ0) (by norm_num)
      _ = 8 / ℓ := by ring
  calc |deriv Real.smoothTransition ((t - (lo - ℓ)) / ℓ) * (1 / ℓ)
          * Real.smoothTransition (((hi + ℓ) - t) / ℓ)
        + Real.smoothTransition ((t - (lo - ℓ)) / ℓ)
          * (deriv Real.smoothTransition (((hi + ℓ) - t) / ℓ) * (-1 / ℓ))|
      ≤ |deriv Real.smoothTransition ((t - (lo - ℓ)) / ℓ) * (1 / ℓ)
          * Real.smoothTransition (((hi + ℓ) - t) / ℓ)|
        + |Real.smoothTransition ((t - (lo - ℓ)) / ℓ)
          * (deriv Real.smoothTransition (((hi + ℓ) - t) / ℓ) * (-1 / ℓ))| := abs_add_le _ _
    _ ≤ 8 / ℓ + 8 / ℓ := add_le_add t1 t2
    _ = 16 / ℓ := by ring

variable {d : ℕ}

/-- The smooth box cutoff: coordinatewise product of the 1-d plateau profiles. -/
noncomputable def boxCutoff (lo hi : Vec d) (ℓ : ℝ) : Vec d → ℝ :=
  fun x => ∏ i, profile (lo i) (hi i) ℓ (x i)

variable {lo hi : Vec d} {ℓ : ℝ}

theorem boxCutoff_apply (x : Vec d) :
    boxCutoff lo hi ℓ x = ∏ i, profile (lo i) (hi i) ℓ (x i) := rfl

/-- Each coordinate factor is `C^∞`. -/
theorem factor_contDiff (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => profile (lo i) (hi i) ℓ (x i)) :=
  profile_contDiff.comp (contDiff_apply ℝ ℝ i)

theorem boxCutoff_contDiff : ContDiff ℝ (⊤ : ℕ∞) (boxCutoff lo hi ℓ) :=
  contDiff_prod (fun i _ => factor_contDiff i)

theorem boxCutoff_nonneg (x : Vec d) : 0 ≤ boxCutoff lo hi ℓ x :=
  Finset.prod_nonneg (fun _ _ => profile_nonneg _)

theorem boxCutoff_le_one (x : Vec d) : boxCutoff lo hi ℓ x ≤ 1 :=
  Finset.prod_le_one (fun _ _ => profile_nonneg _) (fun _ _ => profile_le_one _)

/-- On the core box `x ∈ [lo, hi]`, the cutoff is identically `1`. -/
theorem boxCutoff_eq_one (hℓ : 0 < ℓ) {x : Vec d} (hx : x ∈ Set.Icc lo hi) :
    boxCutoff lo hi ℓ x = 1 := by
  rw [Set.mem_Icc] at hx
  apply Finset.prod_eq_one
  intro i _
  exact profile_eq_one hℓ (hx.1 i) (hx.2 i)

/-- Off the ℓ-enlargement `[lo - ℓ, hi + ℓ]`, the cutoff vanishes. -/
theorem boxCutoff_eq_zero (hℓ : 0 < ℓ) {x : Vec d}
    (hx : x ∉ Set.Icc (fun i => lo i - ℓ) (fun i => hi i + ℓ)) :
    boxCutoff lo hi ℓ x = 0 := by
  rw [Set.mem_Icc, not_and_or] at hx
  rcases hx with h | h
  · rw [Pi.le_def, not_forall] at h
    obtain ⟨i, hi⟩ := h
    push Not at hi
    exact Finset.prod_eq_zero (Finset.mem_univ i) (profile_eq_zero_left hℓ hi.le)
  · rw [Pi.le_def, not_forall] at h
    obtain ⟨i, hi⟩ := h
    push Not at hi
    exact Finset.prod_eq_zero (Finset.mem_univ i) (profile_eq_zero_right hℓ hi.le)

/-- `HasFDerivAt` for the box cutoff, via the finite-product rule on the
coordinate factors. -/
theorem boxCutoff_hasFDerivAt (x : Vec d) :
    HasFDerivAt (boxCutoff lo hi ℓ)
      (∑ i, (∏ j ∈ Finset.univ.erase i, profile (lo j) (hi j) ℓ (x j)) •
        (deriv (profile (lo i) (hi i) ℓ) (x i) •
          (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ))) x := by
  have hfac : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      HasFDerivAt (fun y : Vec d => profile (lo i) (hi i) ℓ (y i))
        (deriv (profile (lo i) (hi i) ℓ) (x i) •
          (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ)) x := by
    intro i _
    have hp : HasDerivAt (profile (lo i) (hi i) ℓ)
        (deriv (profile (lo i) (hi i) ℓ) (x i)) (x i) :=
      (profile_differentiable (lo := lo i) (hi := hi i) (ℓ := ℓ) (x i)).hasDerivAt
    exact HasDerivAt.comp_hasFDerivAt (h₂ := profile (lo i) (hi i) ℓ)
      (f := fun y : Vec d => y i) x hp (hasFDerivAt_apply i x)
  exact HasFDerivAt.finsetProd hfac

/-- The `i`-th partial derivative of the box cutoff: only the `i`-th factor is
differentiated, the rest form the product with `i` removed. -/
theorem boxCutoff_fderiv_single (x : Vec d) (k : Fin d) :
    fderiv ℝ (boxCutoff lo hi ℓ) x (Pi.single k 1) =
      (∏ j ∈ Finset.univ.erase k, profile (lo j) (hi j) ℓ (x j)) *
        deriv (profile (lo k) (hi k) ℓ) (x k) := by
  rw [(boxCutoff_hasFDerivAt x).fderiv]
  simp only [sum_apply, smul_apply, smul_eq_mul,
    ContinuousLinearMap.proj_apply, Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ k]
  simp

/-- **Coordinate derivative bound:** `|∂ᵢ η x| ≤ 16 / ℓ` (with `C = 16`). -/
theorem boxCutoff_deriv_bound (hℓ : 0 < ℓ) (x : Vec d) (k : Fin d) :
    |fderiv ℝ (boxCutoff lo hi ℓ) x (Pi.single k 1)| ≤ 16 / ℓ := by
  rw [boxCutoff_fderiv_single, abs_mul]
  have hprod : |∏ j ∈ Finset.univ.erase k, profile (lo j) (hi j) ℓ (x j)| ≤ 1 := by
    rw [Finset.abs_prod]
    apply Finset.prod_le_one
    · intro j _; exact abs_nonneg _
    · intro j _; rw [abs_of_nonneg (profile_nonneg _)]; exact profile_le_one _
  have hderiv : |deriv (profile (lo k) (hi k) ℓ) (x k)| ≤ 16 / ℓ :=
    profile_deriv_abs_le hℓ _
  calc |∏ j ∈ Finset.univ.erase k, profile (lo j) (hi j) ℓ (x j)|
        * |deriv (profile (lo k) (hi k) ℓ) (x k)|
      ≤ 1 * (16 / ℓ) := mul_le_mul hprod hderiv (abs_nonneg _) (by norm_num)
    _ = 16 / ℓ := one_mul _

/-- **Squared-gradient bound:** `Σᵢ |∂ᵢ η x|² ≤ d · (16/ℓ)²`. -/
theorem boxCutoff_sq_grad_bound (hℓ : 0 < ℓ) (x : Vec d) :
    ∑ i, (fderiv ℝ (boxCutoff lo hi ℓ) x (Pi.single i 1)) ^ 2
      ≤ (d : ℝ) * (16 / ℓ) ^ 2 := by
  calc ∑ i, (fderiv ℝ (boxCutoff lo hi ℓ) x (Pi.single i 1)) ^ 2
      ≤ ∑ _i : Fin d, (16 / ℓ) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        rw [← sq_abs]
        have h := boxCutoff_deriv_bound (lo := lo) (hi := hi) hℓ x i
        nlinarith [abs_nonneg (fderiv ℝ (boxCutoff lo hi ℓ) x (Pi.single i 1)), h]
    _ = (d : ℝ) * (16 / ℓ) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Support-volume bound:** the support of `η` is contained in the enlarged
box, whose volume is `∏ᵢ (hiᵢ − loᵢ + 2ℓ)`. -/
theorem boxCutoff_support_volume_le (hℓ : 0 < ℓ) (hle : lo ≤ hi) :
    volume (Function.support (boxCutoff lo hi ℓ))
      ≤ ENNReal.ofReal (∏ i, (hi i - lo i + 2 * ℓ)) := by
  have hsub : Function.support (boxCutoff lo hi ℓ)
      ⊆ Set.Icc (fun i => lo i - ℓ) (fun i => hi i + ℓ) := by
    intro x hx
    rw [Function.mem_support] at hx
    unfold boxCutoff at hx
    rw [Set.mem_Icc]
    have key : ∀ i, lo i - ℓ ≤ x i ∧ x i ≤ hi i + ℓ := by
      intro i
      have hi0 : profile (lo i) (hi i) ℓ (x i) ≠ 0 :=
        Finset.prod_ne_zero_iff.mp hx i (Finset.mem_univ i)
      refine ⟨?_, ?_⟩
      · by_contra hlt; push Not at hlt
        exact hi0 (profile_eq_zero_left hℓ hlt.le)
      · by_contra hlt; push Not at hlt
        exact hi0 (profile_eq_zero_right hℓ hlt.le)
    exact ⟨fun i => (key i).1, fun i => (key i).2⟩
  calc volume (Function.support (boxCutoff lo hi ℓ))
      ≤ volume (Set.Icc (fun i => lo i - ℓ) (fun i => hi i + ℓ)) := measure_mono hsub
    _ = ∏ i, ENNReal.ofReal ((hi i + ℓ) - (lo i - ℓ)) := Real.volume_Icc_pi
    _ = ∏ i, ENNReal.ofReal (hi i - lo i + 2 * ℓ) := by
        apply Finset.prod_congr rfl
        intro i _; congr 1; ring
    _ = ENNReal.ofReal (∏ i, (hi i - lo i + 2 * ℓ)) := by
        rw [← ENNReal.ofReal_prod_of_nonneg]
        intro i _
        have : lo i ≤ hi i := hle i
        linarith

/-- Bundled smooth box cutoff data (support, range, plateau, and derivative bounds as named fields). -/
structure SmoothBoxCutoff (lo hi : Vec d) (ℓ : ℝ) where
  /-- The cutoff function. -/
  toFun : Vec d → ℝ
  /-- Smoothness. -/
  contDiff : ContDiff ℝ (⊤ : ℕ∞) toFun
  /-- Values lie in `[0, 1]`. -/
  mem_Icc : ∀ x, toFun x ∈ Set.Icc (0 : ℝ) 1
  /-- Identically `1` on the core box `[lo, hi]`. -/
  eq_one_of_mem : ∀ x ∈ Set.Icc lo hi, toFun x = 1
  /-- Vanishes off the ℓ-enlargement `[lo − ℓ, hi + ℓ]`. -/
  eq_zero_of_notMem_enlarged :
    ∀ x, x ∉ Set.Icc (fun i => lo i - ℓ) (fun i => hi i + ℓ) → toFun x = 0
  /-- Coordinate derivative bound with explicit constant `16 / ℓ`. -/
  deriv_bound : ∀ x i, |fderiv ℝ toFun x (Pi.single i 1)| ≤ 16 / ℓ

/-- The concrete smooth box cutoff. -/
noncomputable def smoothBoxCutoff (lo hi : Vec d) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    SmoothBoxCutoff lo hi ℓ where
  toFun := boxCutoff lo hi ℓ
  contDiff := boxCutoff_contDiff
  mem_Icc := fun x => Set.mem_Icc.2 ⟨boxCutoff_nonneg x, boxCutoff_le_one x⟩
  eq_one_of_mem := fun _ hx => boxCutoff_eq_one hℓ hx
  eq_zero_of_notMem_enlarged := fun _ hx => boxCutoff_eq_zero hℓ hx
  deriv_bound := fun x i => boxCutoff_deriv_bound hℓ x i

/-- **Smooth box cutoff existence theorem.**  For any closed box `[lo, hi]` (`lo ≤ hi`) and
margin `ℓ > 0`, there is a `C^∞` cutoff, valued in `[0, 1]`, equal to `1` on the
box, supported in the ℓ-enlargement, with coordinate derivative bound `16/ℓ`,
squared-gradient bound `d·(16/ℓ)²`, and support volume `≤ ∏ᵢ (hiᵢ−loᵢ+2ℓ)`. -/
theorem exists_smoothBoxCutoff (lo hi : Vec d) (ℓ : ℝ) (hℓ : 0 < ℓ) (hle : lo ≤ hi) :
    ∃ η : Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) η ∧
      (∀ x, η x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ x ∈ Set.Icc lo hi, η x = 1) ∧
      (∀ x, x ∉ Set.Icc (fun i => lo i - ℓ) (fun i => hi i + ℓ) → η x = 0) ∧
      (∀ x i, |fderiv ℝ η x (Pi.single i 1)| ≤ 16 / ℓ) ∧
      (∀ x, ∑ i, (fderiv ℝ η x (Pi.single i 1)) ^ 2 ≤ (d : ℝ) * (16 / ℓ) ^ 2) ∧
      volume (Function.support η) ≤ ENNReal.ofReal (∏ i, (hi i - lo i + 2 * ℓ)) :=
  ⟨boxCutoff lo hi ℓ, boxCutoff_contDiff,
    fun x => Set.mem_Icc.2 ⟨boxCutoff_nonneg x, boxCutoff_le_one x⟩,
    fun _ hx => boxCutoff_eq_one hℓ hx,
    fun _ hx => boxCutoff_eq_zero hℓ hx,
    fun x i => boxCutoff_deriv_bound hℓ x i,
    fun x => boxCutoff_sq_grad_bound hℓ x,
    boxCutoff_support_volume_le hℓ hle⟩

end Homogenization
