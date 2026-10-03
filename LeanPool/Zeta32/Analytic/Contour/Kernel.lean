/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Interfaces
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! The logistic density `ρ(y) = (π/2) sech²(πy)` on the line `t = 1/2 + i y`, its
derivative, the kernel `w = 2rρ + iρ'` of `Interfaces.lean`, and integrability of
polynomially bounded functions against them (the proof notes, 5.1). -/

public section

open MeasureTheory Set Filter Topology

namespace Zeta32.Analytic.Contour

noncomputable section

/-- The contour point `t = 1/2 + i y`, written exactly as in `heineIntegrand`. -/
@[expose]
def tpt (y : ℝ) : ℂ := (1/2 : ℂ) + Complex.I * (y : ℂ)

/-- The logistic density `ρ(y) = (π/2) sech²(πy)`. -/
@[expose]
def rho (y : ℝ) : ℝ := Real.pi / 2 / Real.cosh (Real.pi * y) ^ 2

/-- `ρ'(y) = -π² sinh(πy) / cosh³(πy)`. -/
def rhoDeriv (y : ℝ) : ℝ :=
  -(Real.pi ^ 2 * Real.sinh (Real.pi * y) / Real.cosh (Real.pi * y) ^ 3)

lemma tpt_re (y : ℝ) : (tpt y).re = 1/2 := by simp [tpt]

lemma tpt_im (y : ℝ) : (tpt y).im = y := by simp [tpt]

lemma continuous_tpt : Continuous tpt := by unfold tpt; fun_prop

lemma cosh_pi_pos (y : ℝ) : 0 < Real.cosh (Real.pi * y) := Real.cosh_pos _

lemma rho_pos (y : ℝ) : 0 < rho y := by
  unfold rho
  have := cosh_pi_pos y
  positivity

lemma continuous_rho : Continuous rho := by
  unfold rho
  exact continuous_const.div (by fun_prop) fun y => (pow_pos (cosh_pi_pos y) 2).ne'

lemma continuous_rhoDeriv : Continuous rhoDeriv := by
  unfold rhoDeriv
  exact (continuous_const.mul (by fun_prop)).div (by fun_prop)
    (fun y => (pow_pos (cosh_pi_pos y) 3).ne') |>.neg

lemma hasDerivAt_rho (y : ℝ) : HasDerivAt rho (rhoDeriv y) y := by
  have hc : HasDerivAt (fun y : ℝ => Real.cosh (Real.pi * y))
      (Real.sinh (Real.pi * y) * Real.pi) y := by
    simpa using ((hasDerivAt_id y).const_mul Real.pi).cosh
  have hc2 := hc.pow 2
  have h := (hasDerivAt_const y (Real.pi / 2)).div hc2 (pow_pos (cosh_pi_pos y) 2).ne'
  unfold rho rhoDeriv
  convert h using 1
  have h0 := (cosh_pi_pos y).ne'
  simp only [Pi.pow_apply]
  field_simp
  ring

lemma rhoDeriv_eq (y : ℝ) :
    rhoDeriv y = -(2 * Real.pi * Real.tanh (Real.pi * y) * rho y) := by
  unfold rhoDeriv rho
  rw [Real.tanh_eq_sinh_div_cosh]
  have h0 := (cosh_pi_pos y).ne'
  field_simp

lemma wfun_eq (r : ℚ) (y : ℝ) :
    wfun r y = 2 * (r : ℂ) * (rho y : ℂ) + Complex.I * (rhoDeriv y : ℂ) := by
  unfold wfun
  rw [rhoDeriv_eq]
  change (rho y : ℂ) * _ = _
  push_cast
  ring

lemma exp_abs_le_two_cosh (x : ℝ) : Real.exp |x| ≤ 2 * Real.cosh x := by
  rw [← Real.cosh_abs, Real.cosh_eq]
  have := Real.exp_pos (-|x|)
  linarith

lemma inv_cosh_sq_le (x : ℝ) : 1 / Real.cosh x ^ 2 ≤ 4 * Real.exp (-(2 * |x|)) := by
  have h1 := exp_abs_le_two_cosh x
  have hc := Real.cosh_pos x
  have he : Real.exp (-(2 * |x|)) = 1 / Real.exp |x| ^ 2 := by
    rw [← Real.exp_nat_mul, Real.exp_neg, one_div]; push_cast; ring_nf
  rw [he]
  have hep := Real.exp_pos |x|
  rw [div_le_iff₀ (by positivity)]
  field_simp
  nlinarith [mul_self_le_mul_self hep.le h1]

lemma rho_le (y : ℝ) : rho y ≤ 2 * Real.pi * Real.exp (-(2 * Real.pi) * |y|) := by
  have h := inv_cosh_sq_le (Real.pi * y)
  rw [abs_mul, abs_of_pos Real.pi_pos] at h
  unfold rho
  calc Real.pi / 2 / Real.cosh (Real.pi * y) ^ 2
      = Real.pi / 2 * (1 / Real.cosh (Real.pi * y) ^ 2) := by ring
    _ ≤ Real.pi / 2 * (4 * Real.exp (-(2 * (Real.pi * |y|)))) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 2 * Real.pi * Real.exp (-(2 * Real.pi) * |y|) := by ring_nf

lemma abs_rhoDeriv_le (y : ℝ) : |rhoDeriv y| ≤ 2 * Real.pi * rho y := by
  rw [rhoDeriv_eq, abs_neg, abs_mul, abs_mul, abs_of_pos (rho_pos y),
    abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
  have ht : |Real.tanh (Real.pi * y)| ≤ 1 := by
    rw [abs_le]; constructor
    · exact (Real.neg_one_lt_tanh _).le
    · exact (Real.tanh_lt_one _).le
  have := rho_pos y
  have := Real.pi_pos
  have h2 : 0 < 2 * Real.pi * rho y := by positivity
  nlinarith [mul_le_mul_of_nonneg_left ht h2.le]

-- adapted from
-- dtq1997/li2-half-irrationality@d5d8206:Li2Unified/Modular/Base/OriginalContourIntegrable.lean
lemma integrable_abs_pow_exp (n : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ => |x| ^ n * Real.exp (-b * |x|)) := by
  have hp : IntegrableOn (fun x : ℝ => |x| ^ n * Real.exp (-b * |x|)) (Ioi 0) := by
    have h : IntegrableOn (fun x : ℝ => x ^ n * Real.exp (-b * x)) (Ioi 0) := by
      simpa only [Real.rpow_natCast, Real.rpow_one] using
        (integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1)
          (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg n))
          (by norm_num) hb)
    exact h.congr_fun (fun x hx => by rw [abs_of_pos hx]) measurableSet_Ioi
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨?_, hp⟩
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (Homeomorph.neg ℝ).measurableEmbedding]
  simpa only [Function.comp_def, abs_neg, neg_preimage, neg_Iio, neg_zero] using hp

-- adapted from
-- dtq1997/li2-half-irrationality@d5d8206:Li2Unified/Modular/Base/OriginalContourIntegrable.lean
lemma integrable_one_add_abs_pow_exp (n : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ => (1 + |x|) ^ n * Real.exp (-b * |x|)) := by
  have hm : Integrable (fun x : ℝ =>
      (2 : ℝ) ^ (n - 1) * (1 + |x| ^ n) * Real.exp (-b * |x|)) := by
    convert ((integrable_abs_pow_exp 0 hb).add
      (integrable_abs_pow_exp n hb)).const_mul ((2 : ℝ) ^ (n - 1)) using 1
    funext x
    simp only [Pi.add_apply, pow_zero, one_mul]
    ring
  apply hm.mono' (show Continuous (fun x : ℝ =>
    (1 + |x|) ^ n * Real.exp (-b * |x|)) from by fun_prop).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simpa only [one_pow] using mul_le_mul_of_nonneg_right
      (add_pow_le (by norm_num : (0 : ℝ) ≤ 1) (abs_nonneg x) n)
      (Real.exp_pos _).le)

/-- A continuous function with polynomial growth, times a real weight bounded by
`c·ρ`, is integrable. -/
theorem integrable_mul_of_le_rho {f : ℝ → ℂ} {g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {c C : ℝ} {N : ℕ} (hgc : ∀ y, |g y| ≤ c * rho y) (hfb : ∀ y, ‖f y‖ ≤ C * (1 + |y|) ^ N) :
    Integrable (fun y => f y * (g y : ℂ)) := by
  have hdom : Integrable (fun y : ℝ =>
      (|C| * |c| * (2 * Real.pi)) * ((1 + |y|) ^ N * Real.exp (-(2 * Real.pi) * |y|))) :=
    (integrable_one_add_abs_pow_exp N (by positivity)).const_mul _
  refine hdom.mono' (hf.mul (Complex.continuous_ofReal.comp hg)).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 : ‖f y‖ ≤ |C| * (1 + |y|) ^ N :=
    (hfb y).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  have h2 : |g y| ≤ |c| * (2 * Real.pi * Real.exp (-(2 * Real.pi) * |y|)) :=
    (hgc y).trans ((mul_le_mul_of_nonneg_right (le_abs_self c) (rho_pos y).le).trans
      (mul_le_mul_of_nonneg_left (rho_le y) (abs_nonneg c)))
  calc ‖f y‖ * |g y| ≤ (|C| * (1 + |y|) ^ N) *
        (|c| * (2 * Real.pi * Real.exp (-(2 * Real.pi) * |y|))) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem integrable_mul_rho {f : ℝ → ℂ} (hf : Continuous f) {C : ℝ} {N : ℕ}
    (hfb : ∀ y, ‖f y‖ ≤ C * (1 + |y|) ^ N) :
    Integrable (fun y => f y * (rho y : ℂ)) :=
  integrable_mul_of_le_rho hf continuous_rho (c := 1)
    (fun y => by rw [abs_of_pos (rho_pos y), one_mul]) hfb

theorem integrable_mul_rhoDeriv {f : ℝ → ℂ} (hf : Continuous f) {C : ℝ} {N : ℕ}
    (hfb : ∀ y, ‖f y‖ ≤ C * (1 + |y|) ^ N) :
    Integrable (fun y => f y * (rhoDeriv y : ℂ)) :=
  integrable_mul_of_le_rho hf continuous_rhoDeriv abs_rhoDeriv_le hfb

theorem integrable_mul_wfun (r : ℚ) {f : ℝ → ℂ} (hf : Continuous f) {C : ℝ} {N : ℕ}
    (hfb : ∀ y, ‖f y‖ ≤ C * (1 + |y|) ^ N) :
    Integrable (fun y => f y * wfun r y) := by
  have h := ((integrable_mul_rho hf hfb).const_mul (2 * (r : ℂ))).add
    ((integrable_mul_rhoDeriv hf hfb).const_mul Complex.I)
  refine h.congr (Eventually.of_forall fun y => ?_)
  simp only [wfun_eq, Pi.add_apply]
  ring

end

end Zeta32.Analytic.Contour

end
