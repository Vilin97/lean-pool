/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import LeanPool.PLAcceleratedNesterovLean.MorseBott.HessianPL.Basics
import Mathlib.Topology.Order.Compact

/-!
# Hessian coercivity from PŁ — main theorems

Proves `muPL_norm_sq_bound` and `hessian_coercive_on_orthogonal_of_MuPL_impl`,
establishing that the Hessian is μ-coercive on ker(Hess)⊥ under the PŁ condition.
-/

open Filter Topology Metric Submodule Asymptotics

noncomputable section

namespace PLAcceleratedNesterovLean

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- ════════════════════════════════════════════════════════════════════════════
-- § E. PŁ + Taylor → μ · H(v,v) ≤ ‖Hv‖²
-- ════════════════════════════════════════════════════════════════════════════

omit [FiniteDimensional ℝ E] in
/-- Under μ-PŁ at a local minimum, μ · H(v,v) ≤ ‖Hv‖² for all v. -/
lemma muPL_norm_sq_bound (f : E → ℝ) (μ : ℝ) (x₀ v : E)
    (hμ : 0 < μ) (hf : ContDiffAt ℝ 2 f x₀) (hmin : IsLocalMin f x₀)
    (hPL : MuPL f μ x₀) :
    μ * hessian f x₀ v v ≤ ‖hessian f x₀ v‖ ^ 2 := by
  -- Trivial if H(v,v) ≤ 0 (which by PSD means = 0)
  by_cases hvv_pos : hessian f x₀ v v ≤ 0
  · have hvv0 : hessian f x₀ v v = 0 :=
      le_antisymm hvv_pos (hessian_nonneg f x₀ v hf hmin)
    simp only [hvv0, mul_zero, norm_nonneg, pow_succ_nonneg]
  push Not at hvv_pos
  -- H(v,v) > 0. By contradiction, assume μ * H(v,v) > ‖Hv‖².
  by_contra h_contra
  push Not at h_contra
  set H := hessian f x₀
  set Hvv := H v v
  set normHv := ‖H v‖
  set gap := μ * Hvv - normHv ^ 2 with hgap_def
  have hgap_pos : 0 < gap := by linarith
  -- Derivative of fderiv at x₀ is the hessian
  have hhess_deriv : HasFDerivAt (fderiv ℝ f) H x₀ :=
    ((hf.fderiv_right le_rfl).differentiableAt one_ne_zero).hasFDerivAt
  have hdf0 : fderiv ℝ f x₀ = 0 := hmin.fderiv_eq_zero
  -- Gradient approximation: fderiv ℝ f (x₀ + h) - H h =o[𝓝 0] h
  have hgrad_o : (fun h => fderiv ℝ f (x₀ + h) - H h) =o[𝓝 (0 : E)] fun h => h := by
    have := hasFDerivAt_iff_isLittleO_nhds_zero.mp hhess_deriv
    simp_all
  -- Compose with ray t ↦ t • v
  have hray_tend : Tendsto (fun t : ℝ => t • v) (𝓝 0) (𝓝 (0 : E)) := by
    rw [show (0 : E) = (0 : ℝ) • v from (zero_smul ℝ v).symm]
    exact tendsto_id.smul tendsto_const_nhds
  have hgrad_ray : (fun t : ℝ => fderiv ℝ f (x₀ + t • v) - t • H v) =o[𝓝 (0 : ℝ)]
      fun t : ℝ => t • v := by
    refine (hgrad_o.comp_tendsto hray_tend).congr (fun t => ?_) (fun _ => rfl)
    simp only [Function.comp_apply, map_smul]
  -- PŁ along ray
  have hPL_ray : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      f (x₀ + t • v) - f x₀ ≤ (2 * μ)⁻¹ * ‖fderiv ℝ f (x₀ + t • v)‖ ^ 2 := by
    have htend : Tendsto (fun t : ℝ => x₀ + t • v) (𝓝 0) (𝓝 x₀) := by
      have key : Tendsto (fun t : ℝ => x₀ + t • v) (𝓝 0) (𝓝 (x₀ + (0 : ℝ) • v)) :=
        tendsto_const_nhds.add (tendsto_id.smul tendsto_const_nhds)
      simp_all
    exact (htend.eventually hPL).filter_mono nhdsWithin_le_nhds
  -- Taylor bound
  have hTaylor := taylor_ray_isLittleO_pl f x₀ v hf hmin
  -- Choose error tolerances
  have hε : (0 : ℝ) < gap / (4 * μ) := by positivity
  set ε' := gap / (4 * (normHv + 1) * (‖v‖ + 1) * (gap + 1)) with hε'_def
  have hε'_pos : 0 < ε' := by positivity
  -- Extract eventual witnesses
  have hTaylor_bound := hTaylor.bound hε
  have hgrad_bound := hgrad_ray.bound hε'_pos
  have h_pos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t :=
    eventually_nhdsWithin_of_forall fun _ ht => ht
  obtain ⟨t, hT, hG, hPLt, ht_pos⟩ :=
    (hTaylor_bound.and ((hgrad_bound.filter_mono nhdsWithin_le_nhds).and
      (hPL_ray.and h_pos))).exists
  have ht_sq_pos : 0 < t ^ 2 := sq_pos_of_pos ht_pos
  -- Taylor lower bound: f(x₀+tv) - f(x₀) ≥ t²/2 · Hvv - gap/(4μ) · t²
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)] at hT
  have hT_lower : t ^ 2 / 2 * Hvv - gap / (4 * μ) * t ^ 2 ≤
      f (x₀ + t • v) - f x₀ := by linarith [abs_le.mp hT]
  -- Gradient upper bound: ‖fderiv(x₀+tv)‖ ≤ t·‖Hv‖ + ε'·t·‖v‖
  have hG_upper : ‖fderiv ℝ f (x₀ + t • v)‖ ≤ t * normHv + ε' * t * ‖v‖ := by
    have h1 : ‖fderiv ℝ f (x₀ + t • v)‖ ≤ ‖t • H v‖ +
        ‖fderiv ℝ f (x₀ + t • v) - t • H v‖ := by
      calc ‖fderiv ℝ f (x₀ + t • v)‖
          = ‖t • H v + (fderiv ℝ f (x₀ + t • v) - t • H v)‖ := by congr 1; abel
        _ ≤ ‖t • H v‖ + ‖fderiv ℝ f (x₀ + t • v) - t • H v‖ := norm_add_le _ _
    have h2 : ‖t • H v‖ = t * normHv := by
      rw [norm_smul, Real.norm_of_nonneg ht_pos.le]
    have h3 : ‖fderiv ℝ f (x₀ + t • v) - t • H v‖ ≤ ε' * (t * ‖v‖) := by
      calc ‖fderiv ℝ f (x₀ + t • v) - t • H v‖
          ≤ ε' * ‖t • v‖ := hG
        _ = ε' * (|t| * ‖v‖) := by rw [norm_smul, Real.norm_eq_abs]
        _ = ε' * (t * ‖v‖) := by rw [abs_of_pos ht_pos]
    linarith [h1, h2, h3]
  -- PŁ gives upper bound using gradient
  have hPL_upper : f (x₀ + t • v) - f x₀ ≤
      (2 * μ)⁻¹ * (t * normHv + ε' * t * ‖v‖) ^ 2 := by
    calc f (x₀ + t • v) - f x₀
        ≤ (2 * μ)⁻¹ * ‖fderiv ℝ f (x₀ + t • v)‖ ^ 2 := hPLt
      _ ≤ (2 * μ)⁻¹ * (t * normHv + ε' * t * ‖v‖) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact sq_le_sq' (by linarith [norm_nonneg (fderiv ℝ f (x₀ + t • v))]) hG_upper
  -- Combine and factor out t²
  have h_sq_factor : (t * normHv + ε' * t * ‖v‖) ^ 2 =
      t ^ 2 * (normHv + ε' * ‖v‖) ^ 2 := by ring
  -- Divide by t² > 0 to get: Hvv/2 - gap/(4μ) ≤ (normHv + ε'·‖v‖)²/(2μ)
  -- Multiply by 2μ: μ·Hvv - gap/2 ≤ (normHv + ε'·‖v‖)²
  -- Since μ·Hvv = gap + normHv²: gap/2 ≤ 2·normHv·ε'·‖v‖ + (ε'·‖v‖)²
  have hv_ne : v ≠ 0 := by
    intro h
    have : (H v) v = 0 := by simp only [h, map_zero]
    linarith [show Hvv = (H v) v from rfl]
  have hv_norm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_ne
  have h_final : gap / 2 ≤ 2 * normHv * (ε' * ‖v‖) + (ε' * ‖v‖) ^ 2 := by
    have h_combined : t ^ 2 / 2 * Hvv - gap / (4 * μ) * t ^ 2 ≤
        (2 * μ)⁻¹ * (t ^ 2 * (normHv + ε' * ‖v‖) ^ 2) := by
      linarith [h_sq_factor ▸ hPL_upper]
    have h_factored : t ^ 2 * (Hvv / 2 - gap / (4 * μ)) ≤
        t ^ 2 * ((2 * μ)⁻¹ * (normHv + ε' * ‖v‖) ^ 2) := by linarith
    have h_div : Hvv / 2 - gap / (4 * μ) ≤ (2 * μ)⁻¹ * (normHv + ε' * ‖v‖) ^ 2 :=
      le_of_mul_le_mul_left h_factored ht_sq_pos
    have h_eq1 : μ * (Hvv / 2 - gap / (4 * μ)) = μ * Hvv / 2 - gap / 4 := by
      field_simp
    have h_eq2 : μ * ((2 * μ)⁻¹ * (normHv + ε' * ‖v‖) ^ 2) =
        (normHv + ε' * ‖v‖) ^ 2 / 2 := by field_simp
    have h_mul_mu : μ * Hvv / 2 - gap / 4 ≤ (normHv + ε' * ‖v‖) ^ 2 / 2 := by
      have := mul_le_mul_of_nonneg_left h_div hμ.le
      linarith [h_eq1, h_eq2]
    have h_gap_eq : μ * Hvv = gap + normHv ^ 2 := by linarith [hgap_def]
    have h_expand : (normHv + ε' * ‖v‖) ^ 2 =
        normHv ^ 2 + 2 * normHv * (ε' * ‖v‖) + (ε' * ‖v‖) ^ 2 := by ring
    linarith [h_expand]
  -- But ε' is too small for this to hold
  have hε'v_bound : ε' * ‖v‖ < gap / (4 * (normHv + 1) * (gap + 1)) := by
    calc ε' * ‖v‖
        = gap / (4 * (normHv + 1) * (‖v‖ + 1) * (gap + 1)) * ‖v‖ := by rw [hε'_def]
      _ < gap / (4 * (normHv + 1) * (‖v‖ + 1) * (gap + 1)) * (‖v‖ + 1) := by
          exact mul_lt_mul_of_pos_left (lt_add_one _) (by positivity)
      _ = gap / (4 * (normHv + 1) * (gap + 1)) := by field_simp
  have hNHv : (0 : ℝ) ≤ normHv := norm_nonneg (H v)
  have hBp : (0 : ℝ) < gap / (4 * (normHv + 1) * (gap + 1)) := by positivity
  have hBlt1 : gap / (4 * (normHv + 1) * (gap + 1)) < 1 := by
    rw [div_lt_one (by positivity : (0:ℝ) < 4 * (normHv + 1) * (gap + 1))]
    have h_prod := mul_nonneg hNHv hgap_pos.le
    have h_exp : 4 * (normHv + 1) * (gap + 1) =
        4 * normHv * gap + 4 * normHv + 4 * gap + 4 := by ring
    linarith
  have hδp : (0 : ℝ) < ε' * ‖v‖ := mul_pos hε'_pos hv_norm_pos
  have hδlt1 : ε' * ‖v‖ < 1 := lt_trans hε'v_bound hBlt1
  have hstep1 : (ε' * ‖v‖) ^ 2 < ε' * ‖v‖ := by
    have : (ε' * ‖v‖) ^ 2 = (ε' * ‖v‖) * (ε' * ‖v‖) := sq (ε' * ‖v‖)
    rw [this]; exact mul_lt_of_lt_one_right hδp hδlt1
  have hstep2 : 2 * normHv * (ε' * ‖v‖) + (ε' * ‖v‖) ^ 2 <
      (2 * normHv + 1) * (gap / (4 * (normHv + 1) * (gap + 1))) := by
    have h1 : 2 * normHv * (ε' * ‖v‖) ≤
        2 * normHv * (gap / (4 * (normHv + 1) * (gap + 1))) :=
      mul_le_mul_of_nonneg_left hε'v_bound.le (by linarith)
    have h2 : (ε' * ‖v‖) ^ 2 < gap / (4 * (normHv + 1) * (gap + 1)) :=
      lt_trans hstep1 hε'v_bound
    linarith [show (2 * normHv + 1) * (gap / (4 * (normHv + 1) * (gap + 1))) =
        2 * normHv * (gap / (4 * (normHv + 1) * (gap + 1))) +
        gap / (4 * (normHv + 1) * (gap + 1)) from by ring]
  have hstep3 : (2 * normHv + 1) ≤ 2 * (normHv + 1) := by linarith
  have hstep4 : 2 * (normHv + 1) * (gap / (4 * (normHv + 1) * (gap + 1))) =
      gap / (2 * (gap + 1)) := by field_simp; ring
  have hstep5 : gap / (2 * (gap + 1)) < gap / 2 := by
    rw [div_lt_div_iff₀ (by positivity : (0:ℝ) < 2 * (gap + 1)) two_pos]
    linarith [mul_pos hgap_pos hgap_pos]
  linarith [mul_le_mul_of_nonneg_right hstep3 hBp.le]

-- ════════════════════════════════════════════════════════════════════════════
-- § F. Rayleigh quotient minimizer argument
-- ════════════════════════════════════════════════════════════════════════════

/-- Main theorem: Under μ-PŁ at a local minimizer, the Hessian is μ-coercive
    on the orthogonal complement of its kernel. -/
theorem hessian_coercive_on_orthogonal_of_MuPL_impl (f : E → ℝ) (μ : ℝ) (x₀ : E)
    (hμ : 0 < μ) (hf : ContDiffAt ℝ 2 f x₀) (hmin : IsLocalMin f x₀)
    (hPL : MuPL f μ x₀) :
    ∀ v ∈ (hessianKer f x₀).orthogonal,
      hessian f x₀ v v ≥ μ * ‖v‖ ^ 2 := by
  intro v hv
  -- Case v = 0: trivial
  by_cases hv0 : v = 0
  · simp_all
  -- Case v ≠ 0: use Rayleigh quotient minimizer
  set H := hessian f x₀ with hH_def
  set K := hessianKer f x₀ with hK_def
  -- Step 1: The unit sphere of K⊥ is compact and nonempty
  set S := {w : E | w ∈ K.orthogonal ∧ ‖w‖ = 1} with hS_def
  have hS_nonempty : S.Nonempty := by
    refine ⟨‖v‖⁻¹ • v, ?_, ?_⟩
    · exact K.orthogonal.smul_mem _ hv
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]
  -- S is compact (subset of unit sphere, which is compact in finite dim)
  have hS_compact : IsCompact S := by
    apply IsCompact.of_isClosed_subset (isCompact_sphere 0 1)
    · exact IsClosed.inter K.isClosed_orthogonal (isClosed_eq continuous_norm continuous_const)
    · intro w hw
      simp_all
  -- Step 2: H(w,w) attains its minimum c on S
  have hH_cont : ContinuousOn (fun w => H w w) S :=
    (H.cont.clm_apply continuous_id).continuousOn.mono (Set.subset_univ _)
  obtain ⟨w₀, hw₀_mem, hw₀_min⟩ := hS_compact.exists_isMinOn hS_nonempty hH_cont
  set c := H w₀ w₀ with hc_def
  have hw₀_orth : w₀ ∈ K.orthogonal := hw₀_mem.1
  have hw₀_norm : ‖w₀‖ = 1 := hw₀_mem.2
  -- Step 3: H(w,w) ≥ c for all w ∈ S
  have hmin_on : ∀ w ∈ S, c ≤ H w w := fun w hw => hw₀_min hw
  -- Step 4: c > 0
  have hc_nonneg : 0 ≤ c := hessian_nonneg f x₀ w₀ hf hmin
  have hc_pos : 0 < c := by
    rcases eq_or_lt_of_le hc_nonneg with hc0 | hc_pos
    · -- c = 0, so H(w₀,w₀) = 0, then w₀ ∈ ker(H), but w₀ ∈ ker(H)⊥
      exfalso
      have : w₀ ∈ K := mem_hessianKer_of_zero_quad f x₀ w₀ hf hmin (by linarith)
      have : w₀ ∈ K ⊓ K.orthogonal := ⟨this, hw₀_orth⟩
      rw [K.orthogonal_disjoint.eq_bot] at this
      have hw0_ne : w₀ ≠ 0 := by rw [ne_eq, ← norm_eq_zero, hw₀_norm]; exact one_ne_zero
      exact absurd ((Submodule.mem_bot ℝ).mp this) hw0_ne
    · exact hc_pos
  -- Step 5: H(v,v) ≥ c · ‖v‖² for all v ∈ K⊥
  -- (from Rayleigh quotient: H(v,v)/‖v‖² ≥ c for v ≠ 0)
  suffices hc_bound : μ ≤ c by
    -- H(v,v) ≥ c · ‖v‖² ≥ μ · ‖v‖²
    have hv_in_S : ‖v‖⁻¹ • v ∈ S := by
      constructor
      · exact K.orthogonal.smul_mem _ hv
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]
    have hRayleigh : c ≤ H (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) := hmin_on _ hv_in_S
    -- H(‖v‖⁻¹ • v)(‖v‖⁻¹ • v) = ‖v‖⁻² · H(v,v)
    simp only [map_smul, smul_apply, smul_eq_mul] at hRayleigh
    -- c ≤ ‖v‖⁻¹ * (‖v‖⁻¹ * H v v)
    have hv_norm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
    have : c * ‖v‖ ^ 2 ≤ H v v := by
      have h1 := mul_le_mul_of_nonneg_right hRayleigh (by positivity : 0 ≤ ‖v‖ ^ 2)
      have hv_ne : (‖v‖ : ℝ) ≠ 0 := ne_of_gt hv_norm_pos
      have h2 : ‖v‖⁻¹ * (‖v‖⁻¹ * (H v) v) * ‖v‖ ^ 2 = (H v) v := by
        field_simp
      linarith
    linarith [mul_le_mul_of_nonneg_right hc_bound (sq_nonneg ‖v‖)]
  -- Step 6: Prove μ ≤ c
  -- The minimizer w₀ is an eigenvector: H(w₀) = c · innerSL ℝ w₀
  -- This gives ‖H(w₀)‖ = c, and then PŁ gives μ ≤ c.
  --
  -- First-order condition: H(w₀,z) = 0 for z ∈ K⊥ with ⟨w₀,z⟩ = 0
  have h_foc : ∀ z : E, z ∈ K.orthogonal → @inner ℝ E _ w₀ z = 0 →
      H w₀ z = 0 := by
    intro z hz hperp
    -- H(w₀+tz, w₀+tz) ≥ c · ‖w₀+tz‖² for all t
    -- since w₀+tz ∈ K⊥ and ‖w₀+tz‖² > 0 for small t
    by_contra hab
    -- Expand: H(w₀+tz,w₀+tz) = c + 2t·H(w₀,z) + t²·H(z,z)
    -- ‖w₀+tz‖² = 1 + t²‖z‖² (using ⟨w₀,z⟩ = 0)
    -- So: 2t·H(w₀,z) + t²(H(z,z) - c‖z‖²) ≥ 0 for all t where w₀+tz ≠ 0
    -- For small |t|, 2t·H(w₀,z) dominates. Contradiction.
    set a := H w₀ z with ha_def
    -- a ≠ 0
    -- For small t: the Rayleigh quotient of w₀+tz is ≥ c
    -- When z ∈ K⊥ and ⟨w₀,z⟩ = 0, ‖w₀+tz‖² = 1 + t²‖z‖²
    have hnorm_sq : ∀ t : ℝ, ‖w₀ + t • z‖ ^ 2 = 1 + t ^ 2 * ‖z‖ ^ 2 := by
      intro t
      rw [norm_add_sq_real]
      simp only [inner_smul_right, hperp, mul_zero, mul_zero, add_zero,
        norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      rw [hw₀_norm]; ring
    -- For t small enough, w₀ + tz ≠ 0
    -- Use: for any t, w₀+tz ∈ K⊥ and ‖w₀+tz‖ > 0 (for small t)
    -- The Rayleigh quotient H(w₀+tz, w₀+tz)/‖w₀+tz‖² ≥ c
    -- Since the denominator is 1 + t²‖z‖² > 0, we get:
    -- H(w₀+tz,w₀+tz) ≥ c(1 + t²‖z‖²) for all t
    have hRQ : ∀ t : ℝ, H (w₀ + t • z) (w₀ + t • z) ≥ c * (1 + t ^ 2 * ‖z‖ ^ 2) := by
      intro t
      by_cases htz : w₀ + t • z = 0
      · -- w₀ + tz = 0 impossible for small t since ‖w₀‖ = 1
        have h0 : ‖w₀ + t • z‖ = 0 := by rw [htz, norm_zero]
        have h1 : ‖w₀ + t • z‖ ^ 2 = 0 := by rw [h0]; ring
        have h2 := hnorm_sq t
        linarith [mul_nonneg (sq_nonneg t) (sq_nonneg ‖z‖)]
      · have hw_in_S : (‖w₀ + t • z‖⁻¹ • (w₀ + t • z)) ∈ S := by
          constructor
          · exact K.orthogonal.smul_mem _
              (K.orthogonal.add_mem hw₀_orth
                (K.orthogonal.smul_mem _ hz))
          · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr htz)]
        have hRQ_unit := hmin_on _ hw_in_S
        simp only [map_smul, smul_apply, smul_eq_mul] at hRQ_unit
        -- c ≤ ‖w₀+tz‖⁻¹ * (‖w₀+tz‖⁻¹ * H(w₀+tz)(w₀+tz))
        -- = H(w₀+tz)(w₀+tz) / ‖w₀+tz‖²
        have hnorm_pos : 0 < ‖w₀ + t • z‖ := norm_pos_iff.mpr htz
        rw [← hnorm_sq]
        calc c * ‖w₀ + t • z‖ ^ 2
            ≤ (‖w₀ + t • z‖⁻¹ * (‖w₀ + t • z‖⁻¹ * H (w₀ + t • z) (w₀ + t • z))) *
              ‖w₀ + t • z‖ ^ 2 := by
              exact mul_le_mul_of_nonneg_right hRQ_unit (sq_nonneg _)
          _ = H (w₀ + t • z) (w₀ + t • z) := by
              field_simp
    -- Expand H(w₀+tz,w₀+tz) = c + 2ta + t²·H(z,z)
    have hexpand : ∀ t : ℝ, H (w₀ + t • z) (w₀ + t • z) =
        c + 2 * t * a + t ^ 2 * H z z := by
      intro t
      have hsymm := hessian_symmetric f x₀ hf z w₀
      simp only [map_add, add_apply, map_smul,
        smul_apply, smul_eq_mul, hH_def, hc_def, ha_def]
      rw [hsymm]
      ring
    -- So: c + 2ta + t²Hz z ≥ c + ct²‖z‖², i.e., 2ta + t²(Hz z - c‖z‖²) ≥ 0 for all t
    have hineq : ∀ t : ℝ, 2 * t * a + t ^ 2 * (H z z - c * ‖z‖ ^ 2) ≥ 0 := by
      intro t
      have h1 := hRQ t
      rw [hexpand] at h1
      linarith
    -- If a ≠ 0, choosing t small with sign opposite to a gives contradiction
    -- t(2a + t(Hzz - c‖z‖²)) ≥ 0 for all t
    -- At t = 0: value = 0, derivative in t = 2a ≠ 0
    -- So the function t ↦ 2ta + t²(Hzz - c‖z‖²) changes sign near 0. Contradiction.
    set d := H z z - c * ‖z‖ ^ 2 with hd_def
    -- The polynomial p(t) = 2at + dt² = t(2a + dt) ≥ 0 for all t
    -- If a > 0: take t < 0 small, then t < 0 and 2a + dt > 0, so product < 0
    -- If a < 0: take t > 0 small, then t > 0 and 2a + dt < 0, so product < 0
    have ha_ne : a ≠ 0 := hab
    set den₂ := a ^ 2 + d ^ 2 + 1 with hden₂_def
    have hden₂_pos : (0 : ℝ) < den₂ := by positivity
    have hden₂_ne : den₂ ≠ 0 := ne_of_gt hden₂_pos
    have h_at := hineq (-a / den₂)
    have h1 : den₂ ^ 2 * (2 * (-a / den₂) * a + (-a / den₂) ^ 2 * d) =
        a ^ 2 * (d - 2 * den₂) := by field_simp; ring
    have h2 : 0 ≤ den₂ ^ 2 * (2 * (-a / den₂) * a + (-a / den₂) ^ 2 * d) :=
      mul_nonneg (sq_nonneg den₂) h_at
    rw [h1] at h2
    have ha2 : (0 : ℝ) < a ^ 2 := by positivity
    have h_sq := sq_nonneg (2 * d - 1)
    have h_sq_exp : (2 * d - 1) ^ 2 = 4 * d ^ 2 - 4 * d + 1 := by ring
    rw [h_sq_exp] at h_sq
    have h_neg : d - 2 * den₂ < 0 := by linarith [sq_nonneg d]
    linarith [mul_neg_of_pos_of_neg ha2 h_neg]
  -- Eigenvector equation: H(w₀) = c • innerSL ℝ w₀
  have h_eig : H w₀ = c • innerSL ℝ w₀ := by
    ext e
    simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]
    -- Decompose e = ⟨e,w₀⟩ • w₀ + z + u
    -- where z ∈ K⊥ ∩ {w₀}⊥ and u ∈ K
    -- Use orthogonal projection
    set e_K := (orthogonalProjectionOnto K e : E)
    set e_Korth := (orthogonalProjectionOnto K.orthogonal e : E)
    have he_decomp : e = e_K + e_Korth := by
      have h := K.starProjection_add_starProjection_orthogonal e
      simp only [Submodule.starProjection, ContinuousLinearMap.comp_apply,
        Submodule.subtypeL_apply] at h
      exact h.symm
    -- e_Korth ∈ K⊥, decompose it: e_Korth = ⟨e_Korth, w₀⟩ • w₀ + z
    -- where z ∈ K⊥ ∩ {w₀}⊥
    set α := @inner ℝ E _ e_Korth w₀
    set z := e_Korth - α • w₀
    have hz_orth : z ∈ K.orthogonal := by
      apply K.orthogonal.sub_mem
      · exact (orthogonalProjectionOnto K.orthogonal e).property
      · exact K.orthogonal.smul_mem _ hw₀_orth
    have hz_perp : @inner ℝ E _ w₀ z = 0 := by
      simp only [z, inner_sub_right, inner_smul_right, α]
      rw [real_inner_self_eq_norm_sq, hw₀_norm, one_pow,
        mul_one, real_inner_comm w₀ e_Korth, sub_self]
    -- e = α • w₀ + z + e_K
    have he_full : e = α • w₀ + z + e_K := by
      simp only [z]
      rw [he_decomp]
      abel
    -- H(w₀, e_K) = 0: e_K ∈ K = ker(H), by symmetry H(w₀, e_K) = H(e_K, w₀) = 0
    have heK_mem : e_K ∈ K := SetLike.coe_mem (orthogonalProjectionOnto K e)
    have h_ker : H w₀ e_K = 0 := by
      rw [hessian_symmetric f x₀ hf w₀ e_K]
      have hmem : (hessian f x₀).toLinearMap e_K = 0 := LinearMap.mem_ker.mp heK_mem
      simp_all
    -- H(w₀, z) = 0 by first-order condition
    have h_foc_z : H w₀ z = 0 := h_foc z hz_orth hz_perp
    -- H(w₀, eN) = α · c where eN = α • w₀ + z
    have h_eN : H w₀ e_Korth = α * c := by
      have : e_Korth = α • w₀ + z := by simp only [add_sub_cancel, z]
      simp_all
    -- H(w₀, e) = H(w₀, e_K) + H(w₀, e_Korth) = 0 + α·c = α·c
    rw [show e = e_K + e_Korth from he_decomp]
    simp only [map_add]
    rw [h_ker, h_eN, zero_add]
    rw [show @inner ℝ E _ w₀ (e_K + e_Korth) = @inner ℝ E _ w₀ e_K + @inner ℝ E _ w₀ e_Korth from
      inner_add_right _ _ _]
    have hw₀eK : @inner ℝ E _ w₀ e_K = 0 := by
      rw [real_inner_comm]; exact Submodule.inner_right_of_mem_orthogonal heK_mem hw₀_orth
    rw [hw₀eK, zero_add]
    simp only [real_inner_comm, mul_comm, α]
  -- ‖H(w₀)‖ = c
  have h_norm : ‖H w₀‖ = c := by
    rw [h_eig, norm_smul, Real.norm_of_nonneg hc_pos.le, innerSL_apply_norm, hw₀_norm, mul_one]
  -- μ ≤ c from PŁ bound
  have hbound := muPL_norm_sq_bound f μ x₀ w₀ hμ hf hmin hPL
  rw [h_norm] at hbound
  -- μ · c ≤ c², so μ ≤ c
  have hc_sq : c ^ 2 = c * c := sq c
  rw [hc_sq] at hbound
  exact le_of_mul_le_mul_right hbound hc_pos

end PLAcceleratedNesterovLean
