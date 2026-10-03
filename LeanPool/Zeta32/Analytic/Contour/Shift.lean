/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Analytic.Contour.Rectangle

/-! The shift rule of the proof notes, §0 for the logistic functional
`E[φ] = ∫ φ(1/2 + i y) ρ(y) dy`:
for `F` holomorphic on `0 < Re t < 2` with polynomial growth on `1/2 ≤ Re t ≤ 3/2`,
`E[F(t+1)] − E[F(t)] = F'(1)`.
Obtained from `boundaryIntegral_mul_Kc` by letting the height `T → ∞`: on both vertical
edges `π²/sin²(πt) = 2πρ(y)`, and on the horizontal edges `|π²/sin²(πt)| ≤ 16π² e^{-2πT}`. -/

public section

open MeasureTheory Set Filter Topology
open scoped Interval

namespace Zeta32.Analytic.Contour

noncomputable section

-- adapted from
-- dtq1997/li2-half-irrationality@d5d8206:
-- Li2Unified/Modular/Base/OriginalContourHorizontalKernel.lean
lemma complexSin_norm_sq (z : ℂ) :
    ‖Complex.sin z‖ ^ 2 = Real.sin z.re ^ 2 + Real.sinh z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.sin_eq,
    ← Complex.ofReal_sin, ← Complex.ofReal_cos,
    ← Complex.ofReal_sinh, ← Complex.ofReal_cosh,
    ← Complex.ofReal_mul, ← Complex.ofReal_mul,
    Complex.normSq_add_mul_I]
  linear_combination
    (Real.sin z.re) ^ 2 * (Real.cosh_sq z.im) +
    (Real.sinh z.im) ^ 2 * (Real.sin_sq_add_cos_sq z.re)

-- adapted from the same file
lemma complexSinh_abs_im_le_norm_sin (z : ℂ) :
    Real.sinh |z.im| ≤ ‖Complex.sin z‖ := by
  rw [← Real.abs_sinh]
  apply (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp
  rw [sq_abs, complexSin_norm_sq]
  exact le_add_of_nonneg_left (sq_nonneg _)

-- adapted from the same file
lemma exp_quarter_le_sinh {t : ℝ} (ht : 1 ≤ t) :
    Real.exp t / 4 ≤ Real.sinh t := by
  have hp : 2 ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  have hm : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  rw [Real.sinh_eq]
  linarith

-- adapted from the same file
lemma complexSin_pi_norm_ge_exp (z : ℂ) (hz : 1 ≤ |z.im|) :
    Real.exp (Real.pi * |z.im|) / 4 ≤ ‖Complex.sin ((Real.pi : ℂ) * z)‖ := by
  have him : |((Real.pi : ℂ) * z).im| = Real.pi * |z.im| := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, abs_mul, abs_of_pos Real.pi_pos]
  have ht : 1 ≤ Real.pi * |z.im| := by
    have hmul := mul_le_mul_of_nonneg_left hz Real.pi_pos.le
    linarith [Real.two_le_pi]
  exact (exp_quarter_le_sinh ht).trans (him ▸ complexSinh_abs_im_le_norm_sin _)

lemma norm_Kc_le (z : ℂ) (hz : 1 ≤ |z.im|) :
    ‖Kc z‖ ≤ 16 * Real.pi ^ 2 * Real.exp (-(2 * Real.pi) * |z.im|) := by
  have h := complexSin_pi_norm_ge_exp z hz
  have he := Real.exp_pos (Real.pi * |z.im|)
  have hs : 0 < ‖Complex.sin ((Real.pi : ℂ) * z)‖ := lt_of_lt_of_le (by positivity) h
  unfold Kc
  rw [norm_div, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  have hexp : Real.exp (-(2 * Real.pi) * |z.im|) * Real.exp (Real.pi * |z.im|) ^ 2 = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; push_cast; ring_nf; exact Real.exp_zero
  rw [div_le_iff₀ (by positivity)]
  have h2 : (Real.exp (Real.pi * |z.im|) / 4) ^ 2 ≤ ‖Complex.sin ((Real.pi : ℂ) * z)‖ ^ 2 :=
    pow_le_pow_left₀ (by positivity) h 2
  have hpos : 0 ≤ 16 * Real.pi ^ 2 * Real.exp (-(2 * Real.pi) * |z.im|) := by positivity
  calc Real.pi ^ 2 = 16 * Real.pi ^ 2 * Real.exp (-(2 * Real.pi) * |z.im|) *
        (Real.exp (Real.pi * |z.im|) / 4) ^ 2 := by
          rw [div_pow]; linear_combination (-Real.pi ^ 2) * hexp
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 hpos

lemma Kc_add_one (t : ℂ) : Kc (t + 1) = Kc t := by
  unfold Kc
  rw [mul_add, mul_one, Complex.sin_add_pi, neg_sq]

lemma sin_pi_tpt (y : ℝ) :
    Complex.sin ((Real.pi : ℂ) * tpt y) = (Real.cosh (Real.pi * y) : ℂ) := by
  have harg : (Real.pi : ℂ) * tpt y = (Real.pi : ℂ) / 2 + ((Real.pi * y : ℝ) : ℂ) * Complex.I := by
    unfold tpt; push_cast; ring
  rw [harg, Complex.sin_add_mul_I]
  simp only [Complex.sin_pi_div_two, Complex.cos_pi_div_two, one_mul, zero_mul, add_zero]
  exact (Complex.ofReal_cosh (Real.pi * y)).symm

lemma Kc_tpt (y : ℝ) : Kc (tpt y) = 2 * (Real.pi : ℂ) * (rho y : ℂ) := by
  unfold Kc rho
  rw [sin_pi_tpt]
  have h0 : (Real.cosh (Real.pi * y) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (cosh_pi_pos y).ne'
  push_cast
  field_simp

lemma tpt_mem_strip (y : ℝ) : tpt y ∈ strip := by
  constructor <;> simp [tpt_re]; norm_num

lemma tpt_add_one_mem_strip (y : ℝ) : tpt y + 1 ∈ strip := by
  constructor <;> simp [tpt_re] <;> norm_num

lemma zT_re (T : ℝ) : (zT T).re = 1/2 := rfl
lemma zT_im (T : ℝ) : (zT T).im = -T := rfl
lemma wT_re (T : ℝ) : (wT T).re = 3/2 := rfl
lemma wT_im (T : ℝ) : (wT T).im = T := rfl

lemma left_pt (y : ℝ) : (((1/2 : ℝ)) : ℂ) + (y : ℂ) * Complex.I = tpt y := by
  unfold tpt; push_cast; ring

lemma right_pt (y : ℝ) : (((3/2 : ℝ)) : ℂ) + (y : ℂ) * Complex.I = tpt y + 1 := by
  unfold tpt; push_cast; ring

/-- The growth hypothesis on the closed strip `1/2 ≤ Re t ≤ 3/2`. -/
@[expose]
def PolyGrowth (F : ℂ → ℂ) (C : ℝ) (N : ℕ) : Prop :=
  ∀ t : ℂ, 1/2 ≤ t.re → t.re ≤ 3/2 → ‖F t‖ ≤ C * (1 + |t.im|) ^ N

lemma horizontal_bound {F : ℂ → ℂ} {C : ℝ} {N : ℕ} (hg : PolyGrowth F C N) {c : ℝ}
    (hc : 1 ≤ |c|) :
    ‖∫ x : ℝ in (1/2 : ℝ)..(3/2 : ℝ), F ((x : ℂ) + (c : ℂ) * Complex.I) *
        Kc ((x : ℂ) + (c : ℂ) * Complex.I)‖ ≤
      C * (1 + |c|) ^ N * (16 * Real.pi ^ 2 * Real.exp (-(2 * Real.pi) * |c|)) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (1/2 : ℝ)) (b := 3/2)
    (C := C * (1 + |c|) ^ N * (16 * Real.pi ^ 2 * Real.exp (-(2 * Real.pi) * |c|)))
    (f := fun x : ℝ => F ((x : ℂ) + (c : ℂ) * Complex.I) * Kc ((x : ℂ) + (c : ℂ) * Complex.I))
    (fun x hx => by
      rw [Set.uIoc_of_le (by norm_num)] at hx
      have him : ((x : ℂ) + (c : ℂ) * Complex.I).im = c := by simp
      have hre : ((x : ℂ) + (c : ℂ) * Complex.I).re = x := by simp
      rw [norm_mul]
      have h1 := hg ((x : ℂ) + (c : ℂ) * Complex.I) (by rw [hre]; exact hx.1.le)
        (by rw [hre]; exact hx.2)
      have h2 := norm_Kc_le ((x : ℂ) + (c : ℂ) * Complex.I) (by rw [him]; exact hc)
      rw [him] at h1 h2
      exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1))
  have hl : |(3/2 : ℝ) - 1/2| = 1 := by norm_num
  rw [hl, mul_one] at h
  exact h

lemma tendsto_growth_exp (C : ℝ) (N : ℕ) :
    Tendsto (fun T : ℝ => C * (1 + T) ^ N * (16 * Real.pi ^ 2 * Real.exp (-(2 * Real.pi) * T)))
      atTop (𝓝 0) := by
  have h1 : Tendsto (fun T : ℝ => (1 + T) ^ N * Real.exp (-(1 + T))) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero N).comp
      (tendsto_atTop_add_const_left _ 1 tendsto_id)
  have h2 : Tendsto (fun T : ℝ => (|C| * 16 * Real.pi ^ 2 * Real.exp 1) *
      ((1 + T) ^ N * Real.exp (-(1 + T)))) atTop (𝓝 0) := by
    simpa using h1.const_mul (|C| * 16 * Real.pi ^ 2 * Real.exp 1)
  refine squeeze_zero_norm' ?_ h2
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (1 + T) ^ N),
    abs_of_pos (by positivity : (0:ℝ) < 16 * Real.pi ^ 2 * Real.exp (-(2 * Real.pi) * T))]
  have hexp : Real.exp (-(2 * Real.pi) * T) ≤ Real.exp 1 * Real.exp (-(1 + T)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.two_le_pi]
  have hC : |C| * ((1 + T) ^ N * (16 * Real.pi ^ 2 * Real.exp (-(2 * Real.pi) * T))) ≤
      |C| * ((1 + T) ^ N * (16 * Real.pi ^ 2 * (Real.exp 1 * Real.exp (-(1 + T))))) := by
    gcongr
  calc |C| * (1 + T) ^ N * (16 * Real.pi ^ 2 * Real.exp (-(2 * Real.pi) * T))
      = |C| * ((1 + T) ^ N * (16 * Real.pi ^ 2 * Real.exp (-(2 * Real.pi) * T))) := by ring
    _ ≤ _ := hC
    _ = (|C| * 16 * Real.pi ^ 2 * Real.exp 1) * ((1 + T) ^ N * Real.exp (-(1 + T))) := by ring

lemma polyGrowth_line {F : ℂ → ℂ} {C : ℝ} {N : ℕ} (hg : PolyGrowth F C N) (y : ℝ) :
    ‖F (tpt y)‖ ≤ C * (1 + |y|) ^ N := by
  have := hg (tpt y) (by rw [tpt_re]) (by rw [tpt_re]; norm_num)
  rwa [tpt_im] at this

lemma polyGrowth_line_add_one {F : ℂ → ℂ} {C : ℝ} {N : ℕ} (hg : PolyGrowth F C N) (y : ℝ) :
    ‖F (tpt y + 1)‖ ≤ C * (1 + |y|) ^ N := by
  have := hg (tpt y + 1) (by simp [tpt_re]) (by simp [tpt_re]; norm_num)
  simpa [tpt_im] using this

/-- **Shift rule** `E[F(t+1)] − E[F(t)] = F'(1)`. -/
theorem shift_rule {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F strip) {C : ℝ} {N : ℕ}
    (hg : PolyGrowth F C N) :
    (∫ y : ℝ, F (tpt y + 1) * (rho y : ℂ)) - ∫ y : ℝ, F (tpt y) * (rho y : ℂ) = deriv F 1 := by
  have hc0 : Continuous fun y => F (tpt y) :=
    hF.continuousOn.comp_continuous continuous_tpt tpt_mem_strip
  have hc1 : Continuous fun y => F (tpt y + 1) :=
    hF.continuousOn.comp_continuous (continuous_tpt.add continuous_const) tpt_add_one_mem_strip
  have hi0 := integrable_mul_rho hc0 (polyGrowth_line hg)
  have hi1 := integrable_mul_rho hc1 (polyGrowth_line_add_one hg)
  set E0 := ∫ y : ℝ, F (tpt y) * (rho y : ℂ)
  set E1 := ∫ y : ℝ, F (tpt y + 1) * (rho y : ℂ)
  -- the boundary integral as a function of `T`
  set bot : ℝ → ℂ := fun T => ∫ x : ℝ in (1/2 : ℝ)..(3/2 : ℝ),
    F ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) * Kc ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
  set top : ℝ → ℂ := fun T => ∫ x : ℝ in (1/2 : ℝ)..(3/2 : ℝ),
    F ((x : ℂ) + (T : ℂ) * Complex.I) * Kc ((x : ℂ) + (T : ℂ) * Complex.I)
  set V0 : ℝ → ℂ := fun T => ∫ y : ℝ in (-T)..T, F (tpt y) * (rho y : ℂ)
  set V1 : ℝ → ℂ := fun T => ∫ y : ℝ in (-T)..T, F (tpt y + 1) * (rho y : ℂ)
  have hform : ∀ T : ℝ, boundaryIntegral (fun t => F t * Kc t) (zT T) (wT T) =
      bot T - top T + 2 * (Real.pi : ℂ) * Complex.I * (V1 T - V0 T) := by
    intro T
    unfold Zeta32.Analytic.Contour.boundaryIntegral
    simp only [zT_re, zT_im, wT_re, wT_im]
    have hr : (∫ y : ℝ in (-T)..T, F (((3/2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) *
        Kc (((3/2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) =
        2 * (Real.pi : ℂ) * V1 T := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun y _ => ?_
      simp only [right_pt, Kc_add_one, Kc_tpt]
      ring
    have hl : (∫ y : ℝ in (-T)..T, F (((1/2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) *
        Kc (((1/2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) =
        2 * (Real.pi : ℂ) * V0 T := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun y _ => ?_
      simp only [left_pt, Kc_tpt]
      ring
    rw [hr, hl, smul_eq_mul, smul_eq_mul]
    ring
  have hlimV0 : Tendsto V0 atTop (𝓝 E0) :=
    intervalIntegral_tendsto_integral hi0 tendsto_neg_atTop_atBot tendsto_id
  have hlimV1 : Tendsto V1 atTop (𝓝 E1) :=
    intervalIntegral_tendsto_integral hi1 tendsto_neg_atTop_atBot tendsto_id
  have hbot : Tendsto bot atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_growth_exp C N)
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    have h := horizontal_bound hg (c := -T) (by rw [abs_neg, abs_of_pos (by linarith)]; exact hT)
    rwa [abs_neg, abs_of_pos (by linarith)] at h
  have htop : Tendsto top atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_growth_exp C N)
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    have h := horizontal_bound hg (c := T) (by rw [abs_of_pos (by linarith)]; exact hT)
    rwa [abs_of_pos (by linarith)] at h
  have hlim : Tendsto (fun T => bot T - top T + 2 * (Real.pi : ℂ) * Complex.I * (V1 T - V0 T))
      atTop (𝓝 (0 - 0 + 2 * (Real.pi : ℂ) * Complex.I * (E1 - E0))) :=
    (hbot.sub htop).add ((hlimV1.sub hlimV0).const_mul _)
  have hconst : Tendsto (fun T => bot T - top T + 2 * (Real.pi : ℂ) * Complex.I * (V1 T - V0 T))
      atTop (𝓝 (2 * (Real.pi : ℂ) * Complex.I * deriv F 1)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    rw [← hform T, boundaryIntegral_mul_Kc hF hT]
  have huniq := tendsto_nhds_unique hlim hconst
  have h2pi : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    simp [this, Complex.I_ne_zero]
  simp only [sub_zero, zero_add] at huniq
  exact mul_left_cancel₀ h2pi huniq

end

end Zeta32.Analytic.Contour

end
