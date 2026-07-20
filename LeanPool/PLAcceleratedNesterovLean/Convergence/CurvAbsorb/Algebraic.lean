/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import LeanPool.PLAcceleratedNesterovLean.Core.NesterovScheme


/-!
# Curvature Absorption Helper Lemmas

Helper lemmas for the curvature absorption proof (h_curv_absorb_hyp in Basic.lean).
These establish the key perturbation bounds:
1. Step bound: ‖hn‖ ≤ η·‖gn‖ + √η·|ρ|·(‖vn‖ + √η·‖gn‖)
2. MVT bound: ‖P(y-x) - (π y - π x)‖ ≤ ε₁·‖y-x‖
3. Kills-normal bound: ‖P en‖ ≤ ε₁·‖en‖
-/

noncomputable section

namespace PLAcceleratedNesterovLean

variable {d : ℕ}


/-- The Nesterov step satisfies hn = -η·gn + √η·ρ·(vn - √η·gn), so
    ‖hn‖ ≤ η·‖gn‖ + √η·|ρ|·(‖vn‖ + √η·‖gn‖). -/
theorem nesterov_step_bound (f : E d → ℝ) (η ρ : ℝ) (s : NesterovState d) (hη : 0 ≤ η) :
    ‖(nesterovStep f η ρ s).lookahead η - s.lookahead η‖ ≤
    η * ‖gradient f (s.lookahead η)‖ +
    Real.sqrt η * |ρ| * (‖s.v‖ + Real.sqrt η * ‖gradient f (s.lookahead η)‖) := by
  have hse := Real.sqrt_nonneg η
  have key : (nesterovStep f η ρ s).lookahead η - s.lookahead η =
      (-η • gradient f (s.lookahead η)) +
      Real.sqrt η • (ρ • (s.v - Real.sqrt η • gradient f (s.lookahead η))) := by
    simp only [nesterovStep, NesterovState.lookahead]; module
  rw [key]; clear key
  calc ‖(-η • gradient f (s.lookahead η)) +
        Real.sqrt η • (ρ • (s.v - Real.sqrt η • gradient f (s.lookahead η)))‖
      ≤ ‖-η • gradient f (s.lookahead η)‖ +
        ‖Real.sqrt η • (ρ • (s.v - Real.sqrt η • gradient f (s.lookahead η)))‖ :=
        norm_add_le _ _
    _ = η * ‖gradient f (s.lookahead η)‖ +
        Real.sqrt η * (|ρ| * ‖s.v - Real.sqrt η • gradient f (s.lookahead η)‖) := by
        rw [norm_smul ((-η : ℝ)), Real.norm_eq_abs, abs_neg, abs_of_nonneg hη,
            norm_smul ((Real.sqrt η : ℝ)), norm_smul ((ρ : ℝ)),
            Real.norm_of_nonneg hse, Real.norm_eq_abs]
    _ ≤ η * ‖gradient f (s.lookahead η)‖ +
        Real.sqrt η * (|ρ| * (‖s.v‖ + Real.sqrt η * ‖gradient f (s.lookahead η)‖)) := by
        gcongr
        calc ‖s.v - Real.sqrt η • gradient f (s.lookahead η)‖
            ≤ ‖s.v‖ + ‖Real.sqrt η • gradient f (s.lookahead η)‖ := norm_sub_le _ _
          _ = ‖s.v‖ + Real.sqrt η * ‖gradient f (s.lookahead η)‖ := by
              rw [norm_smul, Real.norm_of_nonneg hse]
    _ = η * ‖gradient f (s.lookahead η)‖ +
        Real.sqrt η * |ρ| * (‖s.v‖ + Real.sqrt η * ‖gradient f (s.lookahead η)‖) := by ring

/-- MVT bound: if ‖fderiv π z - P‖ ≤ ε₁ for all z in a ball, then
    ‖P(y-x) - (π y - π x)‖ ≤ ε₁·‖y-x‖ for x, y in the ball. -/
theorem xi_bound_mvt (P : E d →L[ℝ] E d) (π : E d → E d) (x y c : E d) (r : ℝ)
    (hxs : x ∈ Metric.ball c r) (hys : y ∈ Metric.ball c r)
    (hπ_diff : ∀ z ∈ Metric.ball c r, DifferentiableAt ℝ π z)
    (ε₁ : ℝ) (hbound : ∀ z ∈ Metric.ball c r, ‖fderiv ℝ π z - P‖ ≤ ε₁) :
    ‖P (y - x) - (π y - π x)‖ ≤ ε₁ * ‖y - x‖ := by
  have hg_diff : ∀ z ∈ Metric.ball c r, DifferentiableAt ℝ (⇑P - π) z :=
    fun z hz => P.differentiableAt.sub (hπ_diff z hz)
  have hg_bound : ∀ z ∈ Metric.ball c r, ‖fderiv ℝ (⇑P - π) z‖ ≤ ε₁ := by
    intro z hz
    have hfg : fderiv ℝ (⇑P - π) z = P - fderiv ℝ π z :=
      (P.hasFDerivAt.sub (hπ_diff z hz).hasFDerivAt).fderiv
    rw [hfg, ← norm_neg, neg_sub]; exact hbound z hz
  have hmvt := (convex_ball c r).norm_image_sub_le_of_norm_fderiv_le hg_diff hg_bound hxs hys
  convert hmvt using 2
  · rfl
  · simp only [Pi.sub_apply, map_sub]
    abel

/-- If Dπ(π x) kills (x - π x) and ‖Dπ(π x) - P‖ ≤ ε₁, then ‖P(x - π x)‖ ≤ ε₁·‖x - π x‖. -/
theorem proj_normal_bound (P : E d →L[ℝ] E d) (π : E d → E d) (x : E d)
    (hkills : fderiv ℝ π (π x) (x - π x) = 0)
    (ε₁ : ℝ) (hDπ_close : ‖fderiv ℝ π (π x) - P‖ ≤ ε₁) :
    ‖P (x - π x)‖ ≤ ε₁ * ‖x - π x‖ := by
  have key : P (x - π x) = (P - fderiv ℝ π (π x)) (x - π x) := by
    simp only [sub_apply, hkills, sub_zero]
  rw [key]
  calc ‖(P - fderiv ℝ π (π x)) (x - π x)‖
      ≤ ‖P - fderiv ℝ π (π x)‖ * ‖x - π x‖ := (P - fderiv ℝ π (π x)).le_opNorm _
    _ ≤ ε₁ * ‖x - π x‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        calc ‖P - fderiv ℝ π (π x)‖ = ‖-(fderiv ℝ π (π x) - P)‖ := by rw [neg_sub]
          _ = ‖fderiv ℝ π (π x) - P‖ := norm_neg _
          _ ≤ ε₁ := hDπ_close

/-- Core algebraic assembly for curvature absorption.
Given that ‖ξ‖ and ‖Pe‖ each have an ε₁ factor from Dπ continuity,
and all squared norms are bounded by constants times Ln,
conclude δ_curv + proj_err ≤ a/2 * Ln.

The key algebraic steps are:
- Young's inequality: sm·‖w‖·‖h‖ ≤ (sm²·‖w‖² + ‖h‖²)/2  (absorbs √μ')
- ε₁² ≤ ε₁ (since ε₁ ≤ 1), so ‖ξ‖² ≤ ε₁·‖h‖²
- Everything factors as ε₁ · K · Ln, and ε₁ · K ≤ a/2 by hypothesis -/
theorem curv_absorption_algebraic
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    (wn ξn gn Pen hn en : E') (sm sa Ln : ℝ)
    (hsm_nn : 0 ≤ sm) (hsa_pos : 0 < sa) (hLn_nn : 0 ≤ Ln)
    (ε₁ : ℝ) (hε₁_pos : 0 < ε₁) (hε₁_le1 : ε₁ ≤ 1)
    (hξ : ‖ξn‖ ≤ ε₁ * ‖hn‖)
    (hPe : ‖Pen‖ ≤ ε₁ * ‖en‖)
    (C_wh : ℝ) (_hC_wh_nn : 0 ≤ C_wh)
    (hwh : sm ^ 2 * ‖wn‖ ^ 2 + ‖hn‖ ^ 2 ≤ C_wh * Ln)
    (C_h : ℝ) (_hC_h_nn : 0 ≤ C_h)
    (hh_sq : ‖hn‖ ^ 2 ≤ C_h * Ln)
    (C_ge : ℝ) (_hC_ge_nn : 0 ≤ C_ge)
    (hge : ‖gn‖ * ‖en‖ ≤ C_ge * Ln)
    (θ : ℝ) (_hθ_pos : 0 < θ)
    (habs : ε₁ * (C_wh / 2 + sm ^ 2 / 2 * C_h + sa * C_ge) ≤ θ * sa) :
    sm * @inner ℝ _ _ wn ξn + sm ^ 2 / 2 * ‖ξn‖ ^ 2 +
    sa * |@inner ℝ _ _ gn Pen| ≤ θ * sa * Ln := by
  have hCS1 := real_inner_le_norm wn ξn
  have hCS2 := abs_real_inner_le_norm gn Pen
  have hξ_nn := norm_nonneg ξn; have hhn_nn := norm_nonneg hn
  have hen_nn := norm_nonneg en; have hwn_nn := norm_nonneg wn; have hgn_nn := norm_nonneg gn
  have hsm2_nn : 0 ≤ sm ^ 2 / 2 := by positivity
  have hε₁_nn : 0 ≤ ε₁ := le_of_lt hε₁_pos
  have hξ_sq : ‖ξn‖ ^ 2 ≤ ε₁ * ‖hn‖ ^ 2 := by
    have h1 : ‖ξn‖ ≤ ε₁ * ‖hn‖ := hξ
    have h2 : ‖ξn‖ ^ 2 ≤ (ε₁ * ‖hn‖) ^ 2 := sq_le_sq' (by linarith [hξ_nn]) h1
    have h3 : (ε₁ * ‖hn‖) ^ 2 = ε₁ ^ 2 * ‖hn‖ ^ 2 := by ring
    have h4 : ε₁ ^ 2 ≤ ε₁ := by
      calc ε₁ ^ 2 = ε₁ * ε₁ := by ring
        _ ≤ ε₁ * 1 := mul_le_mul_of_nonneg_left hε₁_le1 hε₁_nn
        _ = ε₁ := mul_one _
    calc ‖ξn‖ ^ 2 ≤ ε₁ ^ 2 * ‖hn‖ ^ 2 := by linarith
      _ ≤ ε₁ * ‖hn‖ ^ 2 := mul_le_mul_of_nonneg_right h4 (sq_nonneg _)
  -- Term 1: sm*⟨w,ξ⟩ ≤ ε₁/2 * C_wh * Ln
  have hterm1 : sm * @inner ℝ _ _ wn ξn ≤ ε₁ / 2 * (C_wh * Ln) := by
    have h1 : sm * @inner ℝ _ _ wn ξn ≤ sm * (‖wn‖ * ‖ξn‖) :=
      mul_le_mul_of_nonneg_left hCS1 hsm_nn
    have h2 : ‖ξn‖ ≤ ε₁ * ‖hn‖ := hξ
    have h3 : ‖wn‖ * ‖ξn‖ ≤ ‖wn‖ * (ε₁ * ‖hn‖) :=
      mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    have h5 : 2 * (sm * ‖wn‖ * ‖hn‖) ≤ sm ^ 2 * ‖wn‖ ^ 2 + ‖hn‖ ^ 2 := by
      have := sq_nonneg (sm * ‖wn‖ - ‖hn‖)
      have : (sm * ‖wn‖ - ‖hn‖) ^ 2 = sm^2 * ‖wn‖^2 - 2*sm*‖wn‖*‖hn‖ + ‖hn‖^2 := by ring
      linarith
    -- sm * (‖w‖ * ‖ξ‖) ≤ sm * ‖w‖ * (ε₁ * ‖h‖) = ε₁ * (sm*‖w‖*‖h‖) ≤ ε₁/2 * (sm²‖w‖²+‖h‖²)
    have h6 : sm * (‖wn‖ * ‖ξn‖) ≤ ε₁ * (sm * ‖wn‖ * ‖hn‖) := by
      calc sm * (‖wn‖ * ‖ξn‖) ≤ sm * (‖wn‖ * (ε₁ * ‖hn‖)) :=
              mul_le_mul_of_nonneg_left h3 hsm_nn
        _ = ε₁ * (sm * ‖wn‖ * ‖hn‖) := by ring
    have h7 : ε₁ * (sm * ‖wn‖ * ‖hn‖) ≤ ε₁ / 2 * (sm ^ 2 * ‖wn‖ ^ 2 + ‖hn‖ ^ 2) := by
      linarith [mul_le_mul_of_nonneg_left h5 hε₁_nn]
    have h8 : ε₁ / 2 * (sm ^ 2 * ‖wn‖ ^ 2 + ‖hn‖ ^ 2) ≤ ε₁ / 2 * (C_wh * Ln) := by
      apply mul_le_mul_of_nonneg_left hwh; linarith
    linarith
  -- Term 2: sm²/2 * ‖ξ‖² ≤ ε₁ * sm²/2 * C_h * Ln
  have hterm2 : sm ^ 2 / 2 * ‖ξn‖ ^ 2 ≤ ε₁ * (sm ^ 2 / 2 * (C_h * Ln)) := by
    have h2a : sm ^ 2 / 2 * ‖ξn‖ ^ 2 ≤ sm ^ 2 / 2 * (ε₁ * ‖hn‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hξ_sq hsm2_nn
    have h2b : sm ^ 2 / 2 * (ε₁ * ‖hn‖ ^ 2) = ε₁ * (sm ^ 2 / 2 * ‖hn‖ ^ 2) := by ring
    have h2c : sm ^ 2 / 2 * ‖hn‖ ^ 2 ≤ sm ^ 2 / 2 * (C_h * Ln) :=
      mul_le_mul_of_nonneg_left hh_sq hsm2_nn
    linarith [mul_le_mul_of_nonneg_left h2c hε₁_nn]
  -- Term 3: sa*|⟨g,Pe⟩| ≤ ε₁ * sa * C_ge * Ln
  have hterm3 : sa * |@inner ℝ _ _ gn Pen| ≤ ε₁ * (sa * (C_ge * Ln)) := by
    have h3a : |@inner ℝ _ _ gn Pen| ≤ ‖gn‖ * (ε₁ * ‖en‖) := by
      calc |@inner ℝ _ _ gn Pen| ≤ ‖gn‖ * ‖Pen‖ := hCS2
        _ ≤ ‖gn‖ * (ε₁ * ‖en‖) := by
            exact mul_le_mul_of_nonneg_left hPe hgn_nn
    have h3d : sa * |@inner ℝ _ _ gn Pen| ≤ sa * (‖gn‖ * (ε₁ * ‖en‖)) :=
      mul_le_mul_of_nonneg_left h3a (le_of_lt hsa_pos)
    have h3e : sa * (‖gn‖ * (ε₁ * ‖en‖)) = ε₁ * (sa * (‖gn‖ * ‖en‖)) := by ring
    have h3c : sa * (‖gn‖ * ‖en‖) ≤ sa * (C_ge * Ln) :=
      mul_le_mul_of_nonneg_left hge (le_of_lt hsa_pos)
    linarith [mul_le_mul_of_nonneg_left h3c hε₁_nn]
  -- Assembly: total ≤ ε₁ * K * Ln ≤ θ*sa * Ln
  have htotal : sm * @inner ℝ _ _ wn ξn + sm ^ 2 / 2 * ‖ξn‖ ^ 2 +
      sa * |@inner ℝ _ _ gn Pen| ≤
      ε₁ * ((C_wh / 2 + sm ^ 2 / 2 * C_h + sa * C_ge) * Ln) := by linarith
  linarith [mul_le_mul_of_nonneg_right habs hLn_nn]

end PLAcceleratedNesterovLean
