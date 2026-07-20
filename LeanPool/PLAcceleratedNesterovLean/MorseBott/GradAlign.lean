/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import LeanPool.PLAcceleratedNesterovLean.MorseBott.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Gradient Alignment Lemma

Under μ-PŁ at a local min x₀, proves `fderiv(x) = 0 ↔ fderiv(x)|_{T⊥} = 0`
for x near x₀. Uses Taylor remainder bounds and a Hessian perturbation argument.
-/

open Filter Topology InnerProductSpace Submodule Set

noncomputable section

namespace PLAcceleratedNesterovLean

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- ═══════════════════════════════════════════════════════════════
-- § Helper: Taylor remainder bound using double MVT
-- ═══════════════════════════════════════════════════════════════

omit [FiniteDimensional ℝ E] in
private lemma hasDerivAt_line' (x v : E) (t : ℝ) :
    HasDerivAt (fun s => x + s • v) v t := by
  have := (hasDerivAt_id t).smul_const v
  simp_all

omit [FiniteDimensional ℝ E] in
private lemma hasDerivAt_f_line' {f : E → ℝ} {x v : E} {t : ℝ}
    (hf : ContDiffAt ℝ 2 f (x + t • v)) :
    HasDerivAt (fun s => f (x + s • v)) (fderiv ℝ f (x + t • v) v) t :=
  (hf.differentiableAt two_ne_zero).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_line' x v t)

omit [FiniteDimensional ℝ E] in
private lemma hasDerivAt_fderiv_line_eval' {f : E → ℝ} {x v : E} {t : ℝ}
    (hf : ContDiffAt ℝ 2 f (x + t • v)) :
    HasDerivAt (fun s => fderiv ℝ f (x + s • v) v)
      (hessian f (x + t • v) v v) t := by
  have hΦ : HasDerivAt (fun s => fderiv ℝ f (x + s • v))
      ((hessian f (x + t • v)) v) t :=
    ((hf.fderiv_right le_rfl).differentiableAt
      one_ne_zero).hasFDerivAt.comp_hasDerivAt
      t (hasDerivAt_line' x v t)
  have h := hΦ.clm_apply (hasDerivAt_const t v)
  simp_all

omit [FiniteDimensional ℝ E] in
private lemma taylor_remainder_bound' {f : E → ℝ} {x v : E}
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 2 f (x + t • v))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖hessian f (x + t • v) v v‖ ≤ C * ‖v‖ ^ 2) :
    ‖f (x + v) - f x - fderiv ℝ f x v‖ ≤ C * ‖v‖ ^ 2 := by
  have hmvt1 : ∀ t ∈ Icc (0:ℝ) 1,
      ‖fderiv ℝ f (x + t • v) v - fderiv ℝ f x v‖ ≤ C * ‖v‖ ^ 2 * (t - 0) := by
    have hd : ∀ s ∈ Icc (0:ℝ) 1,
        HasDerivWithinAt (fun s => fderiv ℝ f (x + s • v) v)
          (hessian f (x + s • v) v v) (Icc 0 1) s :=
      fun s hs => (hasDerivAt_fderiv_line_eval' (hf s hs)).hasDerivWithinAt
    have hb : ∀ s ∈ Ico (0:ℝ) 1,
        ‖hessian f (x + s • v) v v‖ ≤ C * ‖v‖ ^ 2 :=
      fun s hs => hbound s ⟨hs.1, le_of_lt hs.2⟩
    have h := norm_image_sub_le_of_norm_deriv_le_segment' hd hb
    simp_all
  have hk_deriv : ∀ s ∈ Icc (0:ℝ) 1,
      HasDerivWithinAt
        (fun s => f (x + s • v) - f x - s * (fderiv ℝ f x v))
        (fderiv ℝ f (x + s • v) v - fderiv ℝ f x v) (Icc 0 1) s := by
    intro s hs
    have h1 := (hasDerivAt_f_line' (hf s hs)).hasDerivWithinAt (s := Icc 0 1)
    have h2 : HasDerivWithinAt (fun _ => f x) 0 (Icc 0 1) s :=
      hasDerivWithinAt_const s _ _
    have h3 : HasDerivWithinAt (fun s => s * fderiv ℝ f x v)
        (1 * fderiv ℝ f x v) (Icc 0 1) s :=
      (hasDerivAt_id s |>.mul_const _).hasDerivWithinAt
    have := (h1.sub h2).sub h3
    convert this using 1
    · rfl
    · rfl
    · funext t
      rfl
    · rw [sub_zero, one_mul]
  have hk_bound : ∀ s ∈ Ico (0:ℝ) 1,
      ‖fderiv ℝ f (x + s • v) v - fderiv ℝ f x v‖ ≤ C * ‖v‖ ^ 2 := by
    intro s hs
    have h1 := hmvt1 s ⟨hs.1, le_of_lt hs.2⟩
    calc ‖fderiv ℝ f (x + s • v) v - fderiv ℝ f x v‖
        ≤ C * ‖v‖ ^ 2 * (s - 0) := h1
      _ ≤ C * ‖v‖ ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (by linarith [hs.2]) (mul_nonneg hC (sq_nonneg _))
      _ = C * ‖v‖ ^ 2 := mul_one _
  have hmvt2 := norm_image_sub_le_of_norm_deriv_le_segment_01' hk_deriv hk_bound
  simp_all

-- ═══════════════════════════════════════════════════════════════
-- § Main theorem
-- ═══════════════════════════════════════════════════════════════

lemma gradient_alignment_impl (f : E → ℝ) (μ : ℝ) (x₀ : E) (hμ : 0 < μ)
    (hf : ContDiffAt ℝ 2 f x₀) (hmin : IsLocalMin f x₀) (hPL : MuPL f μ x₀) :
    ∃ W ∈ 𝓝 x₀, ∀ x ∈ W,
      fderiv ℝ f x = 0 ↔
        (∀ w : (hessianKer f x₀).orthogonal, fderiv ℝ f x (w : E) = 0) := by
  set T := hessianKer f x₀
  set H := hessian f x₀
  have hDf_zero : fderiv ℝ f x₀ = 0 := hmin.fderiv_eq_zero
  -- Smooth ball: ContDiffAt propagates to nearby points
  obtain ⟨r_smooth, hr_smooth_pos, hr_smooth⟩ :
      ∃ r > 0, ∀ z, dist z x₀ < r → ContDiffAt ℝ 2 f z :=
    Metric.eventually_nhds_iff.mp (hf.eventually (by simp))
  have hDf_cont : ContinuousAt (fderiv ℝ f) x₀ :=
    hf.continuousAt_fderiv two_ne_zero
  have hH_cont : ContinuousAt (hessian f) x₀ :=
    (hf.fderiv_right le_rfl).continuousAt_fderiv one_ne_zero
  -- ═══ Neighborhoods ═══
  set ε := μ / 4 with hε_def
  have hε_pos : (0 : ℝ) < ε := by linarith
  -- PŁ ball
  obtain ⟨r_PL, hr_PL_pos, hr_PL⟩ :
      ∃ r > 0, ∀ z : E, dist z x₀ < r →
        f z - f x₀ ≤ (2 * μ)⁻¹ * ‖fderiv ℝ f z‖ ^ 2 := by
    rwa [← Metric.eventually_nhds_iff]
  -- Local min ball
  obtain ⟨r_min, hr_min_pos, hr_min⟩ :
      ∃ r > 0, ∀ z : E, dist z x₀ < r → f x₀ ≤ f z := by
    rwa [← Metric.eventually_nhds_iff]
  -- Hessian ball: ‖hessian f z - H‖ ≤ ε for z near x₀
  -- We use: dist(hessian f z, H) < ε near x₀ (by continuity) and then
  -- convert dist to norm. The CLM diamond requires care.
  obtain ⟨r_hess, hr_hess_pos, hr_hess⟩ :
      ∃ r > 0, ∀ z : E, dist z x₀ < r → ‖hessian f z - H‖ ≤ ε := by
    -- hessian f is continuous, so dist(hessian f z, hessian f x₀) < ε eventually
    have hev : ∀ᶠ z in 𝓝 x₀, dist (hessian f z) H < ε :=
      hH_cont.eventually (Metric.ball_mem_nhds H hε_pos)
    obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff.mp hev
    refine ⟨r, hr, fun z hz => ?_⟩
    have hdist := hb hz
    exact le_of_lt (by simpa [dist_eq_norm] using hdist)
  -- Combined radius
  set R := min r_PL (min r_min (min r_hess r_smooth))
  have hR_pos : 0 < R := lt_min hr_PL_pos (lt_min hr_min_pos (lt_min hr_hess_pos hr_smooth_pos))
  -- Gradient smallness
  obtain ⟨r_grad, hr_grad_pos, hr_grad⟩ :
      ∃ r > 0, ∀ z : E, dist z x₀ < r → ‖fderiv ℝ f z‖ < μ * R / 6 := by
    have : ∀ᶠ z in 𝓝 x₀, ‖fderiv ℝ f z‖ < μ * R / 6 := by
      have : ‖fderiv ℝ f x₀‖ < μ * R / 6 := by
        simp_all
      exact hDf_cont.norm.preimage_mem_nhds (gt_mem_nhds this)
    exact Metric.eventually_nhds_iff.mp this
  set r := min r_grad (R / 3)
  have hr_pos : 0 < r := lt_min hr_grad_pos (by linarith)
  refine ⟨Metric.ball x₀ r, Metric.ball_mem_nhds x₀ hr_pos, ?_⟩
  intro x hx
  rw [Metric.mem_ball] at hx
  have hx_R3 : dist x x₀ < R / 3 := lt_of_lt_of_le hx (min_le_right _ _)
  constructor
  -- ═══ Forward ═══
  · intro h w; simp only [h, zero_apply]
  -- ═══ Backward ═══
  · intro hw
    suffices hnorm : ‖fderiv ℝ f x‖ = 0 by exact norm_eq_zero.mp hnorm
    by_contra hne
    have hpos : 0 < ‖fderiv ℝ f x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    -- Riesz representative
    set g := (toDual ℝ E).symm (fderiv ℝ f x)
    have hg_inner : ∀ w : E, ⟪g, w⟫_ℝ = fderiv ℝ f x w := fun _ => toDual_symm_apply
    have hg_norm : ‖g‖ = ‖fderiv ℝ f x‖ := LinearIsometryEquiv.norm_map _ _
    -- g ∈ T
    have hg_mem : g ∈ T := by
      rw [show T = T.orthogonal.orthogonal from (orthogonal_orthogonal T).symm]
      exact (mem_orthogonal' T.orthogonal g).mpr fun u hu => by
        rw [hg_inner u]; exact hw ⟨u, hu⟩
    -- H(g) = 0
    have hH_g : H g = 0 := LinearMap.mem_ker.mp hg_mem
    -- Gradient step v = -(2/μ)·g
    set v := -(2 / μ) • g
    have hv_mem : v ∈ T := T.smul_mem _ hg_mem
    have hH_v : H v = 0 := LinearMap.mem_ker.mp hv_mem
    -- Df(x)(v) = -(2/μ)·‖Df(x)‖²
    have hDfv : fderiv ℝ f x v = -(2 / μ) * ‖fderiv ℝ f x‖ ^ 2 := by
      have h1 : fderiv ℝ f x v = ⟪g, v⟫_ℝ := (hg_inner v).symm
      rw [h1, show v = -(2 / μ) • g from rfl, real_inner_smul_right,
          real_inner_self_eq_norm_sq, hg_norm]
    -- ‖v‖ = (2/μ)·‖Df(x)‖
    have hv_norm : ‖v‖ = 2 / μ * ‖fderiv ℝ f x‖ := by
      change ‖-(2 / μ) • g‖ = 2 / μ * ‖fderiv ℝ f x‖
      rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (div_pos two_pos hμ), hg_norm]
    -- ‖v‖ < R/3
    have hv_small : ‖v‖ < R / 3 := by
      rw [hv_norm]
      have : ‖fderiv ℝ f x‖ < μ * R / 6 := hr_grad x (lt_of_lt_of_le hx (min_le_left _ _))
      calc 2 / μ * ‖fderiv ℝ f x‖ < 2 / μ * (μ * R / 6) :=
              mul_lt_mul_of_pos_left this (div_pos two_pos hμ)
        _ = R / 3 := by field_simp; ring
    set y := x + v
    -- Distance control
    have hx_R : dist x x₀ < R := by linarith [hx_R3]
    have hy_R : dist y x₀ < R := by
      calc dist y x₀ ≤ dist x x₀ + ‖v‖ := by
              rw [dist_eq_norm, dist_eq_norm, show x + v - x₀ = (x - x₀) + v from by abel]
              exact norm_add_le _ _
        _ < R / 3 + R / 3 := add_lt_add hx_R3 hv_small
        _ < R := by linarith
    -- Segment stays near x₀
    have hseg_R : ∀ t ∈ Icc (0:ℝ) 1, dist (x + t • v) x₀ < R := by
      intro t ⟨ht0, ht1⟩
      calc dist (x + t • v) x₀
          ≤ dist x x₀ + ‖t • v‖ := by
              rw [dist_eq_norm, dist_eq_norm, show x + t • v - x₀ = (x - x₀) + t • v from by abel]
              exact norm_add_le _ _
        _ ≤ dist x x₀ + ‖v‖ := by
              gcongr; rw [norm_smul, Real.norm_eq_abs]
              exact mul_le_of_le_one_left (norm_nonneg v) (abs_le.mpr ⟨by linarith, ht1⟩)
        _ < R / 3 + R / 3 := add_lt_add hx_R3 hv_small
        _ < R := by linarith
    -- Key inequalities
    have hPL_x : f x - f x₀ ≤ (2 * μ)⁻¹ * ‖fderiv ℝ f x‖ ^ 2 :=
      hr_PL x (lt_of_lt_of_le hx_R (min_le_left _ _))
    have hmin_y : f x₀ ≤ f y :=
      hr_min y (lt_of_lt_of_le hy_R (le_trans (min_le_right _ _) (min_le_left _ _)))
    -- Hessian bilinear bound on segment
    have hhess_vv : ∀ t ∈ Icc (0:ℝ) 1,
        ‖hessian f (x + t • v) v v‖ ≤ ε * ‖v‖ ^ 2 := by
      intro t ht
      have hH_v_v : (H v) v = 0 := congr_fun (congr_arg DFunLike.coe hH_v) v
      calc ‖hessian f (x + t • v) v v‖
          = ‖(hessian f (x + t • v) - H) v v + H v v‖ := by
              congr 1; simp only [sub_apply, sub_add_cancel]
        _ = ‖(hessian f (x + t • v) - H) v v‖ := by rw [hH_v_v, add_zero]
        _ ≤ ‖(hessian f (x + t • v) - H) v‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ (‖hessian f (x + t • v) - H‖ * ‖v‖) * ‖v‖ := by
              gcongr; exact ContinuousLinearMap.le_opNorm _ _
        _ = ‖hessian f (x + t • v) - H‖ * ‖v‖ ^ 2 := by ring
        _ ≤ ε * ‖v‖ ^ 2 := by
              gcongr
              exact hr_hess _ (lt_of_lt_of_le (hseg_R t ht)
                (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
    -- Taylor bound
    have htaylor : f y - f x - fderiv ℝ f x v ≤ ε * ‖v‖ ^ 2 := by
      have : ‖f (x + v) - f x - fderiv ℝ f x v‖ ≤ ε * ‖v‖ ^ 2 :=
        taylor_remainder_bound'
          (fun t ht => hr_smooth _ (lt_of_lt_of_le (hseg_R t ht)
            (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))))
          ε hε_pos.le hhess_vv
      exact le_trans (le_abs_self _) (Real.norm_eq_abs _ ▸ this)
    -- ‖v‖²
    have hv_sq : ‖v‖ ^ 2 = (2 / μ) ^ 2 * ‖fderiv ℝ f x‖ ^ 2 := by rw [hv_norm]; ring
    -- Descent: f(y) ≤ f(x) - μ⁻¹·‖Df(x)‖²
    have h_descent : f y ≤ f x - μ⁻¹ * ‖fderiv ℝ f x‖ ^ 2 := by
      rw [hDfv, hv_sq] at htaylor
      -- htaylor: f y - f x - (-(2/μ))·‖Df‖² ≤ ε·(2/μ)²·‖Df‖²
      -- f y ≤ f x - (2/μ)·‖Df‖² + ε·(2/μ)²·‖Df‖² = f x - μ⁻¹·‖Df‖²
      have hcomp : -(2 / μ) + ε * (2 / μ) ^ 2 = -(μ⁻¹) := by
        rw [hε_def]; field_simp; ring
      nlinarith [sq_nonneg ‖fderiv ℝ f x‖]
    -- Contradiction chain
    -- f(x₀) ≤ f(y) ≤ f(x) - μ⁻¹·D² ≤ f(x₀) + (2μ)⁻¹·D² - μ⁻¹·D²
    -- = f(x₀) - (2μ)⁻¹·D² < f(x₀)
    have h_combined : μ⁻¹ * ‖fderiv ℝ f x‖ ^ 2 ≤ (2 * μ)⁻¹ * ‖fderiv ℝ f x‖ ^ 2 :=
      le_trans (by linarith [hmin_y]) hPL_x
    have h_mu : μ⁻¹ = 2 * (2 * μ)⁻¹ := by field_simp
    set X := (2 * μ)⁻¹ * ‖fderiv ℝ f x‖ ^ 2 with hX_def
    have h_2X : μ⁻¹ * ‖fderiv ℝ f x‖ ^ 2 = 2 * X := by rw [h_mu, hX_def]; ring
    have h_nonpos : X ≤ 0 := by linarith [h_2X, h_combined]
    have h_nonneg : 0 ≤ (2 * μ)⁻¹ * ‖fderiv ℝ f x‖ ^ 2 := by positivity
    have h_eq : (2 * μ)⁻¹ * ‖fderiv ℝ f x‖ ^ 2 = 0 := le_antisymm h_nonpos h_nonneg
    have h_sq_zero : ‖fderiv ℝ f x‖ ^ 2 = 0 :=
      (mul_eq_zero.mp h_eq).resolve_left (by positivity)
    have h_zero : ‖fderiv ℝ f x‖ = 0 := by
      rcases sq_eq_zero_iff.mp h_sq_zero with h; exact h
    linarith

end PLAcceleratedNesterovLean
