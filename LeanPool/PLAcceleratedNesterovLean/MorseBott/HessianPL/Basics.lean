/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import LeanPool.PLAcceleratedNesterovLean.MorseBott.Defs
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Topology.Order.Compact

/-!
# Helper lemmas for Hessian coercivity from PŁ

These lemmas support the proof of `hessian_coercive_on_orthogonal_of_MuPL`
in `Submanifold.lean`. The proof uses the Rayleigh quotient minimizer
approach: the minimum of H(w,w) on the unit sphere of ker(H)⊥ is attained
at an eigenvector, and PŁ forces this minimum to be ≥ μ.
-/

open Filter Topology Metric Submodule Asymptotics

noncomputable section

namespace PLAcceleratedNesterovLean

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- ════════════════════════════════════════════════════════════════════════════
-- § A. Taylor expansion along a ray (re-proved; private in HessianCoercive)
-- ════════════════════════════════════════════════════════════════════════════

omit [FiniteDimensional ℝ E] in
/-- Taylor expansion of a C² function along a ray from a local minimum:
    f(x₀ + t•v) - f(x₀) = (t²/2) · H(v,v) + o(t²)  as t → 0⁺.
    (Copy of `taylor_ray_isLittleO` from HessianCoercive.lean.) -/
lemma taylor_ray_isLittleO_pl (f : E → ℝ) (x₀ v : E)
    (hf : ContDiffAt ℝ 2 f x₀) (hmin : IsLocalMin f x₀) :
    (fun t : ℝ => f (x₀ + t • v) - f x₀ - t ^ 2 / 2 * hessian f x₀ v v) =o[𝓝[>] (0 : ℝ)]
      fun t => t ^ 2 := by
  -- Extract an open ball where f is C² (hence differentiable)
  obtain ⟨u, hu, h'u⟩ : ∃ u ∈ 𝓝 x₀, ContDiffOn ℝ 2 f u :=
    hf.contDiffOn le_rfl (by simp)
  rcases Metric.mem_nhds_iff.mp hu with ⟨R, hR_pos, hR_sub⟩
  have hf_diff_ball : ∀ y ∈ Metric.ball x₀ R, HasFDerivAt f (fderiv ℝ f y) y := by
    intro y hy
    exact ((h'u.mono hR_sub y hy).contDiffAt (Metric.isOpen_ball.mem_nhds hy)).differentiableAt
      two_ne_zero |>.hasFDerivAt
  have hhess : HasFDerivAt (fderiv ℝ f) (hessian f x₀) x₀ :=
    ((hf.fderiv_right le_rfl).differentiableAt one_ne_zero).hasFDerivAt
  have hfx₀ : fderiv ℝ f x₀ = 0 := hmin.fderiv_eq_zero
  -- Handle v = 0 trivially
  by_cases hv0 : v = 0
  · simp_all
  -- v ≠ 0: scale v to fit in the ball
  have hv_norm : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  set c := R / (2 * ‖v‖) with hc_def
  have hc_pos : 0 < c := div_pos hR_pos (mul_pos two_pos hv_norm)
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  set w := c • v with hw_def
  have hw_norm_lt : ‖w‖ < R := by
    rw [hw_def, norm_smul, Real.norm_of_nonneg hc_pos.le, hc_def]
    calc R / (2 * ‖v‖) * ‖v‖ = R / 2 := by field_simp
      _ < R := by linarith
  -- Apply taylor_approx_two_segment on ball x₀ R
  -- Section variables: hf expects ∀ x ∈ interior s, HasFDerivAt f (f' x) x
  have key := (convex_ball x₀ R).taylor_approx_two_segment
    (f := f) (f' := fderiv ℝ f) (f'' := hessian f x₀)
    (fun y hy => hf_diff_ball y (by rwa [Metric.isOpen_ball.interior_eq] at hy))
    (Metric.mem_ball_self hR_pos)
    hhess.hasFDerivWithinAt
    (v := (0 : E)) (w := w)
    (by rw [add_zero, Metric.isOpen_ball.interior_eq]; exact Metric.mem_ball_self hR_pos)
    (by rw [add_zero, Metric.isOpen_ball.interior_eq]
        simp_all)
  simp only [smul_zero, add_zero, hfx₀, map_zero, zero_apply,
    smul_eq_mul, mul_zero, sub_zero] at key
  -- key : (fun h => f(x₀ + h • w) - f(x₀) - (h²/2) * H(w,w)) =o[𝓝[>] 0] (h²)
  -- Rescale: compose with (· * c⁻¹) to go from w back to v
  have h_tend : Tendsto (· * c⁻¹) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (· * c⁻¹) (𝓝 (0 : ℝ)) (𝓝 (0 * c⁻¹)) :=
        tendsto_id.mul tendsto_const_nhds
      simp only [zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall fun t ht =>
        mul_pos ht (inv_pos.mpr hc_pos)
  have key2 := key.comp_tendsto h_tend
  have h_simpl : ∀ t : ℝ,
      f (x₀ + (t * c⁻¹) • w) - f x₀ - (t * c⁻¹) ^ 2 / 2 * (hessian f x₀ w w) =
      f (x₀ + t • v) - f x₀ - t ^ 2 / 2 * hessian f x₀ v v := by
    intro t
    have h1 : (t * c⁻¹) • w = t • v := by
      rw [hw_def, smul_smul, show t * c⁻¹ * c = t from by field_simp]
    have h2 : hessian f x₀ w w = c * (c * hessian f x₀ v v) := by
      simp only [hw_def, map_smul, smul_apply, smul_eq_mul]
    rw [h1, h2]; field_simp
  have key3 := key2.congr (fun t => h_simpl t) (fun _ => rfl)
  -- key3 : ... =o[𝓝[>] 0] (fun t => (t * c⁻¹)^2)
  -- (t * c⁻¹)^2 = O(t^2), so the result follows
  refine key3.trans_isBigO ?_
  change ((fun h => h ^ 2) ∘ fun x => x * c⁻¹) =O[𝓝[>] 0] fun t => t ^ 2
  simp only [Function.comp_def]
  have : (fun t : ℝ => (t * c⁻¹) ^ 2) = fun t => c⁻¹ ^ 2 * t ^ 2 := by ext t; ring
  rw [this]
  exact isBigO_const_mul_self _ _ _

-- ════════════════════════════════════════════════════════════════════════════
-- § B. Hessian symmetry for C² functions
-- ════════════════════════════════════════════════════════════════════════════

omit [FiniteDimensional ℝ E] in
/-- The Hessian of a C² function is symmetric: H(v,w) = H(w,v). -/
lemma hessian_symmetric (f : E → ℝ) (x₀ : E) (hf : ContDiffAt ℝ 2 f x₀) (v w : E) :
    hessian f x₀ v w = hessian f x₀ w v := by
  -- Extract neighborhood where f is differentiable
  obtain ⟨u, hu, h'u⟩ : ∃ u ∈ 𝓝 x₀, ContDiffOn ℝ 2 f u :=
    hf.contDiffOn le_rfl (by simp)
  rcases Metric.mem_nhds_iff.mp hu with ⟨r, hr_pos, hr_sub⟩
  have hdf : ∀ᶠ y in 𝓝 x₀, HasFDerivAt f (fderiv ℝ f y) y := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr_pos)] with y hy
    exact ((h'u.mono hr_sub y hy).contDiffAt
      (Metric.isOpen_ball.mem_nhds hy)).differentiableAt two_ne_zero |>.hasFDerivAt
  exact second_derivative_symmetric_of_eventually
    hdf
    (((hf.fderiv_right le_rfl).differentiableAt one_ne_zero).hasFDerivAt)
    v w

-- ════════════════════════════════════════════════════════════════════════════
-- § C. Hessian is PSD at a local minimum
-- ════════════════════════════════════════════════════════════════════════════

omit [FiniteDimensional ℝ E] in
/-- At a local minimum, the Hessian is positive semi-definite: H(v,v) ≥ 0. -/
lemma hessian_nonneg (f : E → ℝ) (x₀ v : E)
    (hf : ContDiffAt ℝ 2 f x₀) (hmin : IsLocalMin f x₀) :
    0 ≤ hessian f x₀ v v := by
  by_contra h
  push Not at h
  have htaylor := taylor_ray_isLittleO_pl f x₀ v hf hmin
  have hε : (0 : ℝ) < -(hessian f x₀ v v) / 4 := by linarith
  have hbound := htaylor.bound hε
  have hmin_ray : ∀ᶠ t in 𝓝[>] (0 : ℝ), f x₀ ≤ f (x₀ + t • v) := by
    have htend : Tendsto (fun t : ℝ => x₀ + t • v) (𝓝 0) (𝓝 x₀) := by
      have key : Tendsto (fun t : ℝ => x₀ + t • v) (𝓝 0) (𝓝 (x₀ + (0 : ℝ) • v)) :=
        tendsto_const_nhds.add (tendsto_id.smul tendsto_const_nhds)
      simp_all
    exact (htend.eventually hmin).filter_mono nhdsWithin_le_nhds
  have h_pos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t :=
    eventually_nhdsWithin_of_forall fun _ ht => ht
  obtain ⟨t, hb, hm, ht_pos⟩ := (hbound.and (hmin_ray.and h_pos)).exists
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)] at hb
  have ht_sq_pos : 0 < t ^ 2 := sq_pos_of_pos ht_pos
  have h_abs := abs_le.mp hb
  have h_upper : f (x₀ + t • v) - f x₀ ≤
      t ^ 2 / 2 * hessian f x₀ v v + -(hessian f x₀ v v) / 4 * t ^ 2 := by linarith [h_abs.2]
  have h_neg : t ^ 2 / 2 * hessian f x₀ v v + -(hessian f x₀ v v) / 4 * t ^ 2 =
      t ^ 2 / 4 * hessian f x₀ v v := by ring
  have h_prod : t ^ 2 / 4 * hessian f x₀ v v < 0 :=
    mul_neg_of_pos_of_neg (by linarith) h
  linarith

-- ════════════════════════════════════════════════════════════════════════════
-- § D. PSD + symmetric → H(v,v) = 0 implies v ∈ ker(H)
-- ════════════════════════════════════════════════════════════════════════════

omit [FiniteDimensional ℝ E] in
/-- For a PSD symmetric Hessian, if H(v,v) = 0 then v ∈ ker(H). -/
lemma mem_hessianKer_of_zero_quad (f : E → ℝ) (x₀ v : E)
    (hf : ContDiffAt ℝ 2 f x₀) (hmin : IsLocalMin f x₀)
    (hzero : hessian f x₀ v v = 0) :
    v ∈ hessianKer f x₀ := by
  rw [hessianKer, LinearMap.mem_ker]
  ext w
  simp only [zero_apply]
  -- Discriminant argument: H(v+tw, v+tw) ≥ 0 for all t ∈ ℝ
  -- Expanding: 2t·H(v,w) + t²·H(w,w) ≥ 0 for all t
  by_contra hvw
  have hpsd : ∀ t : ℝ, 0 ≤ hessian f x₀ (v + t • w) (v + t • w) :=
    fun t => hessian_nonneg f x₀ (v + t • w) hf hmin
  have hexpand : ∀ t : ℝ, hessian f x₀ (v + t • w) (v + t • w) =
      2 * t * hessian f x₀ v w + t ^ 2 * hessian f x₀ w w := by
    intro t
    have hsymm := hessian_symmetric f x₀ hf w v
    simp only [map_add, add_apply, map_smul,
      smul_apply, smul_eq_mul]
    rw [hsymm, hzero]
    ring
  set a := hessian f x₀ v w with ha_def
  set b := hessian f x₀ w w with hb_def
  set den := a ^ 2 + b ^ 2 + 1 with hden_def
  have hden_pos : (0 : ℝ) < den := by positivity
  have h_at_t₀ := hpsd (-a / den)
  rw [hexpand] at h_at_t₀
  have ha_ne : a ≠ 0 := hvw
  have hden_ne : den ≠ 0 := ne_of_gt hden_pos
  have h1 : den ^ 2 * (2 * (-a / den) * a + (-a / den) ^ 2 * b) = a ^ 2 * (b - 2 * den) := by
    field_simp; ring
  have h2 : 0 ≤ den ^ 2 * (2 * (-a / den) * a + (-a / den) ^ 2 * b) :=
    mul_nonneg (sq_nonneg den) h_at_t₀
  rw [h1] at h2
  have ha2 : (0 : ℝ) < a ^ 2 := by positivity
  have h_sq := sq_nonneg (2 * b - 1)
  have h_sq_exp : (2 * b - 1) ^ 2 = 4 * b ^ 2 - 4 * b + 1 := by ring
  rw [h_sq_exp] at h_sq
  have h_neg : b - 2 * den < 0 := by linarith [sq_nonneg b]
  linarith [mul_neg_of_pos_of_neg ha2 h_neg]

end PLAcceleratedNesterovLean
