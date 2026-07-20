/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import LeanPool.PLAcceleratedNesterovLean.Core.EmbeddedManifold
import LeanPool.PLAcceleratedNesterovLean.Convergence.LocalGeometry.Main
import LeanPool.PLAcceleratedNesterovLean.Convergence.Coercivity.Main
import LeanPool.PLAcceleratedNesterovLean.Convergence.LyapunovContraction.Main
import LeanPool.PLAcceleratedNesterovLean.Convergence.Bootstrap.Main
import LeanPool.PLAcceleratedNesterovLean.Convergence.MotionError.Main
import LeanPool.PLAcceleratedNesterovLean.Convergence.CurvAbsorb.Assembly
import Mathlib.Analysis.Calculus.LocalExtr.Basic


/-!
# Local Convergence Argument

This file contains the per-base-point local convergence argument, extracted
from MainTheorem for build parallelism. For each m⋆ ∈ M, the theorem chain
`local_fiberwise_geometry`, `lyapunov_coercivity`,
`motion_bounds_curvature_error`, `lyapunov_contraction`, and
`bootstrap_total_displacement` produces a ball around m⋆ where the Nesterov
iterates converge at the accelerated rate exp(-k / √(L / ((1-θ)²·μ_minus))).
-/

noncomputable section

namespace PLAcceleratedNesterovLean

open scoped Topology NNReal
open Manifold


/-- Local convergence at a single base point m⋆ ∈ M. -/
private abbrev localConvergenceAtBasePointProof
    {d : ℕ} (hd : 0 < d)
    (L : ℝ≥0) (hL : 0 < (L : ℝ))
    (μ : ℝ) (hμ : 0 < μ) (hμ_le_L : μ ≤ ↑L)
    (μ_minus : ℝ) (hμ_minus : 0 < μ_minus) (hμ_minus_lt : μ_minus < μ)
    (θ : ℝ) (hθ : 0 < θ) (hθ_lt1 : θ < 1)
    (f : E d → ℝ)
    (S : Set (E d))
    (hrange : S = argminSet f)
    (U : Set (E d))
    (hTub_sub : IsTubularNeighborhoodOfSubmanifold S U)
    (hPL : PolyakLojasiewicz f μ U)
    (hf_C2 : ContDiffOn ℝ 2 f U)
    (hf_lip : LipschitzOnWith (↑L) (gradient f) U)
    (π : E d → E d)
    (hπ_on_U : ∀ x ∈ U, π x ∈ S ∧ dist x (π x) = Metric.infDist x S)
    (hπ_fix : ∀ x ∈ S, π x = x)
    (hπ_in_S : ∀ x, π x ∈ S)
    (hgrad_zero : ∀ x ∈ S, gradient f x = 0)
    (mstar : E d) (hmstar : mstar ∈ S) :
    let η := 1 / (L : ℝ)
    let ρ := (1 - Real.sqrt (μ_minus * η)) / (1 + Real.sqrt (μ_minus * η))
    ∃ (α : ℝ), 0 < α ∧
      Metric.ball mstar α ⊆ U ∧
      ∀ x₁ ∈ Metric.ball mstar α,
        (∀ k, (nesterovSeq f η ρ x₁ k).lookahead η ∈ U) ∧
        HasAcceleratedRate f
          (fun k => (nesterovSeq f η ρ x₁ k).lookahead η) (↑L) ((1 - θ) ^ 2 * μ_minus) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let η := 1 / (L : ℝ)
  let ρ := (1 - Real.sqrt (μ_minus * η)) / (1 + Real.sqrt (μ_minus * η))
  have hS_argmin : S = argminSet f := hrange
  have hμ' : 0 < μ_minus := hμ_minus
  have hμ'_lt : μ_minus < μ := hμ_minus_lt
  have hη_pos : (0 : ℝ) < η := one_div_pos.mpr hL
  -- ── local_fiberwise_geometry ───────────────────────────────────
  -- Produces U₊(m⋆), ε > 0 with:
  --   (a) normal Hessian ≥ μ_minus  (b) quadratic growth
  --   (c) strong aiming        (d) D²f ≥ -εI on U₊
  have hlem1 : ∃ (U_plus : Set (E d)) (ε : ℝ),
      IsOpen U_plus ∧ mstar ∈ U_plus ∧ 0 < ε ∧
      ε ≤ Real.sqrt (μ_minus / η) ∧
      IsCompact (closure U_plus) ∧ closure U_plus ⊆ U ∧
      Convex ℝ U_plus ∧
      -- (a) Normal Hessian lower bound
      (∀ x ∈ U_plus, ∀ ξ : E d, fderiv ℝ π (π x) ξ = 0 →
        hessianQuadForm f x ξ ≥ μ_minus * ‖ξ‖ ^ 2) ∧
      -- (b) Quadratic growth
      (∀ x ∈ U_plus, f x - fStar f ≥ μ_minus / 2 * (Metric.infDist x S) ^ 2) ∧
      -- (c) Strong aiming
      (∀ x ∈ U_plus, @inner ℝ _ _ (gradient f x) (x - π x) ≥
        f x - fStar f + μ_minus / 2 * ‖x - π x‖ ^ 2) ∧
      -- (d) Hessian lower bound
      (∀ x ∈ U_plus, ∀ ξ : E d,
        hessianQuadForm f x ξ ≥ -ε * ‖ξ‖ ^ 2) ∧
      -- (e) Normal Hessian ≥ μ at mstar
      (∀ ξ : E d, fderiv ℝ π mstar ξ = 0 →
        hessianQuadForm f mstar ξ ≥ μ * ‖ξ‖ ^ 2) ∧
      -- (f) Fiber segments from U_plus stay in U
      (∀ x ∈ U_plus, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        π x + t • (x - π x) ∈ U) := by
    obtain ⟨U_plus, ε, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ :=
      local_fiberwise_geometry hd f L hL μ hμ μ_minus hμ_minus hμ_minus_lt η rfl
        (one_div_pos.mpr hL) S hS_argmin U hTub_sub hPL
        hf_C2 π hπ_on_U hgrad_zero mstar hmstar
    exact ⟨U_plus, ε, h1, h2, h6, h7, h3, h4, h5, h8, h9, h10, h11, h12, h13⟩
  obtain ⟨U_plus, ε, hU_open, hm_in, hε_pos, hε_le, hU_cpt, hU_sub,
          hU_convex, _hNormHess, hQG, hStrAim, hHessLow, _hNormHess_mu, hfiber_U⟩ := hlem1
  -- Derive DifferentiableOn and LipschitzOnWith on U_plus from U hypotheses
  have hf_diffOn_Up : DifferentiableOn ℝ f U_plus :=
    (hf_C2.differentiableOn two_ne_zero).mono
      (subset_closure.trans hU_sub)
  have hf_lip_Up : LipschitzOnWith L (gradient f) U_plus :=
    hf_lip.mono (subset_closure.trans hU_sub)
  -- ── Define P = Dπ(m⋆), the tangent projector at the base point ──
  -- Freezing the tangent space at m⋆ isolates the curvature error ξ_n and makes
  -- it absorbable after shrinking the local patch.
  set P := fderiv ℝ π mstar with hP_def
  -- ── Bridge: connect our hand-rolled π to the canonical PLMB projection ──
  have hS_ne' : S.Nonempty := ⟨mstar, hmstar⟩
  obtain ⟨π', hπ'_on_U, _, _, _, _, _, _, hπ'_diff, hπ'_self_adj, hπ'_C1⟩ :=
    tubular_neighborhood_projection hTub_sub hS_ne'
  have hπ_eq_on_U' : ∀ y ∈ U, π y = π' y := by
    intro y hyU
    have h1 := hπ_on_U y hyU
    have h2 := hπ'_on_U y hyU
    obtain ⟨_, _, huniq⟩ := hTub_sub.uniqueProj y hyU
    exact (huniq (π y) ⟨h1.1, h1.2⟩).trans
      (huniq (π' y) ⟨h2.1, by rw [dist_eq_norm]; exact h2.2⟩).symm
  have h_evt_eq' : π =ᶠ[𝓝 mstar] π' :=
    (hTub_sub.isOpen.eventually_mem (hTub_sub.subset hmstar)).mono
      (fun y hy => hπ_eq_on_U' y hy)
  have h_fderiv_eq' : fderiv ℝ π mstar = fderiv ℝ π' mstar :=
    h_evt_eq'.fderiv_eq
  -- Dπ is continuous at mstar (from π' being C¹ at mstar + bridge)
  have hDπ_cont : ContinuousAt (fun x => fderiv ℝ π x) mstar := by
    have hCA_π' : ContinuousAt (fderiv ℝ π') mstar :=
      (hπ'_C1 mstar hmstar).continuousAt_fderiv one_ne_zero
    exact hCA_π'.congr (h_evt_eq'.fderiv.symm)
  -- P is self-adjoint (from tubular_neighborhood_projection property 9)
  have hP_self_adj : ∀ x y : E d, @inner ℝ _ _ (P x) y = @inner ℝ _ _ x (P y) := by
    simp_all
  -- P is idempotent (from π ∘ π = π, differentiated at m⋆ ∈ S)
  have hP_idem : ∀ x : E d, P (P x) = P x := by
    -- π ∘ π = π everywhere (π maps into S and fixes S)
    have h_pipi : ∀ x, π (π x) = π x := fun x => hπ_fix (π x) (hπ_in_S x)
    -- π is differentiable at mstar (transferred from canonical π')
    have hπ_diff : DifferentiableAt ℝ π mstar :=
      h_evt_eq'.differentiableAt_iff.mpr (hπ'_diff mstar hmstar)
    -- fderiv (π ∘ π) = fderiv π (since π ∘ π = π as functions)
    have h_eq : fderiv ℝ (fun x => π (π x)) mstar = fderiv ℝ π mstar := by
      simp_all
    -- Chain rule: fderiv (π ∘ π) = (fderiv π mstar) ∘ (fderiv π mstar)
    have hπm : π mstar = mstar := hπ_fix mstar hmstar
    have h_chain : fderiv ℝ (fun x => π (π x)) mstar =
        (fderiv ℝ π mstar).comp (fderiv ℝ π mstar) := by
      have hπ_diff_at_πm : DifferentiableAt ℝ π (π mstar) := by rwa [hπm]
      have := fderiv_comp mstar hπ_diff_at_πm hπ_diff
      rwa [hπm] at this
    -- Combine: P ∘ P = P
    have h_comp_eq : (fderiv ℝ π mstar).comp (fderiv ℝ π mstar) = fderiv ℝ π mstar := by
      rw [← h_chain, h_eq]
    intro x
    have := ContinuousLinearMap.ext_iff.mp h_comp_eq x
    simp only [ContinuousLinearMap.comp_apply] at this
    exact this
  have hmu4_le_L : μ_minus ≤ ↑L := by linarith
  have hμη_lt1_pre : μ_minus * η < 1 := by
    change μ_minus * (1 / ↑L) < 1
    rw [mul_one_div, div_lt_one hL]
    linarith
  -- ── lyapunov_coercivity ────────────────────────────────────────
  -- Coercivity of the Lyapunov function: ‖v‖² + μ'‖e‖² ≤ C_coer · L_n
  have hπ_metric_Up : ∀ x ∈ U_plus, dist x (π x) = Metric.infDist x S := by
    intro x hx; exact (hπ_on_U x (hU_sub (subset_closure hx))).2
  have hP_ortho : ∀ v : E d, ‖v‖ ^ 2 = ‖P v‖ ^ 2 + ‖v - P v‖ ^ 2 :=
    fun v => pythagorean_proj P hP_self_adj hP_idem v
  obtain ⟨C_coer, C_Ψ, hC_coer, hC_Ψ, hcoer_bound⟩ :=
    lyapunov_coercivity hd f L hL μ_minus (by linarith : (0:ℝ) < μ_minus) η rfl
      (one_div_pos.mpr hL) hμη_lt1_pre ρ rfl S hS_argmin π hπ_fix hπ_in_S
      P hP_idem hP_self_adj hP_ortho U_plus hπ_metric_Up hQG
  -- ── motion_bounds_curvature_error ──────────────────────────────
  -- Produces R, C_g, C_v, C_h, C_mov, C_ξ with gradient/velocity/step
  -- bounds and curvature error estimate ‖ξ_n‖ ≤ C_ξ √η √L_n.
  -- (Omitted as intermediate; its outputs feed into lyapunov_contraction.)
  -- ── lyapunov_contraction ───────────────────────────────────────
  -- After shrinking neighborhood: ∃ Ω ∋ m⋆, R > 0, such that
  --   L_{n+1} ≤ (1 − a) · L_n  whenever  x_n, x'_n ∈ Ω, L_n ≤ R²
  have hlem4 : ∃ (Ω : Set (E d)) (R : ℝ),
      IsOpen Ω ∧ 0 < R ∧ mstar ∈ Ω ∧ Ω ⊆ U ∧ Ω ⊆ U_plus ∧
      ∀ (x₁ : E d) (n : ℕ),
        let s := nesterovSeq f η ρ x₁ n
        let a := Real.sqrt (μ_minus * η)
        s.x ∈ Ω → s.lookahead η ∈ Ω →
        lyapunov P μ_minus π f η ρ x₁ n ≤ R ^ 2 →
        lyapunov P μ_minus π f η ρ x₁ (n + 1) ≤
          (1 - (1 - θ) * a) * lyapunov P μ_minus π f η ρ x₁ n := by
    -- ── Prerequisites for lyapunov_contraction ──
    have hη_pos : (0 : ℝ) < η := one_div_pos.mpr hL
    have hε_bound : ε * η ≤ Real.sqrt (μ_minus * η) := by
      have h_nn : (0:ℝ) ≤ ε * η := mul_nonneg (le_of_lt hε_pos) (le_of_lt hη_pos)
      rw [Real.le_sqrt h_nn (mul_nonneg (by linarith : (0:ℝ) ≤ μ_minus) (le_of_lt hη_pos))]
      have hε_sq : ε ^ 2 ≤ μ_minus / η := by
        have h1 := hε_le
        have h2 := Real.sq_sqrt (div_nonneg
            (by linarith : (0:ℝ) ≤ μ_minus) (le_of_lt hη_pos))
        have := pow_le_pow_left₀ (le_of_lt hε_pos) h1 2
        linarith
      have h_sq_η := sq_nonneg η
      have h_prod_sq : (ε * η) ^ 2 = ε ^ 2 * η ^ 2 := by ring
      have h_cancel : (μ_minus / η) * η ^ 2 = μ_minus * η := by field_simp
      calc (ε * η) ^ 2 = ε ^ 2 * η ^ 2 := h_prod_sq
        _ ≤ (μ_minus / η) * η ^ 2 := mul_le_mul_of_nonneg_right hε_sq h_sq_η
        _ = μ_minus * η := h_cancel
    have hμη_lt1 : μ_minus * η < 1 := by
      exact hμη_lt1_pre
    have hπ_kills_normal : ∀ x ∈ U_plus,
        fderiv ℝ π (π x) (x - π x) = 0 := by
      intro x hx
      -- x ∈ U_plus  ⟹  x ∈ U  (since closure U_plus ⊆ U)
      have hxU : x ∈ U := hU_sub (subset_closure hx)
      -- π(x) ∈ S ⊆ U
      have hπxS : π x ∈ S := (hπ_on_U x hxU).1
      have hπxU : π x ∈ U := hTub_sub.subset hπxS
      -- S is nonempty (range of a function on a connected, hence nonempty, type)
      have hS_ne : S.Nonempty := ⟨mstar, hmstar⟩
      -- Obtain the canonical projection π' with all 10 properties
      obtain ⟨π', hπ'_on_U, _, _, _, _, _, hπ'_kills, _, _, _⟩ :=
        tubular_neighborhood_projection hTub_sub hS_ne
      -- Both π and π' agree on U: they pick the unique nearest point in S
      have hπ_eq_on_U : ∀ y ∈ U, π y = π' y := by
        intro y hyU
        have h1 := hπ_on_U y hyU   -- π y ∈ S ∧ dist y (π y) = infDist y S
        have h2 := hπ'_on_U y hyU  -- π' y ∈ S ∧ ‖y - π' y‖ = infDist y S
        obtain ⟨_, _, huniq⟩ := hTub_sub.uniqueProj y hyU
        exact (huniq (π y) ⟨h1.1, h1.2⟩).trans
          (huniq (π' y) ⟨h2.1, by rw [dist_eq_norm]; exact h2.2⟩).symm
      -- π and π' agree on the open set U containing π(x), so same fderiv
      have h_evt_eq : π =ᶠ[𝓝 (π x)] π' :=
        (hTub_sub.isOpen.eventually_mem hπxU).mono
          (fun y hy => hπ_eq_on_U y hy)
      -- Conclude from property 7 of π'
      have h := hπ'_kills x hxU       -- fderiv ℝ π' (π' x) (x - π' x) = 0
      rw [← hπ_eq_on_U x hxU] at h    -- fderiv ℝ π' (π x) (x - π x) = 0
      rwa [← h_evt_eq.fderiv_eq] at h  -- fderiv ℝ π (π x) (x - π x) = 0
    -- ── Apply lyapunov_contraction ──
    -- Total perturbation absorption (curvature + projector-freezing error)
    have h_curv_absorb_hyp : ∃ R_abs : ℝ, 0 < R_abs ∧ ∀ (x₁ : E d) (n : ℕ),
        (nesterovSeq f η ρ x₁ n).x ∈ Metric.ball mstar R_abs →
        (nesterovSeq f η ρ x₁ n).lookahead η ∈ Metric.ball mstar R_abs →
        lyapunov P μ_minus π f η ρ x₁ n ≤ R_abs ^ 2 →
        let sn := nesterovSeq f η ρ x₁ n
        let gn := gradient f (sn.lookahead η)
        let en := sn.lookahead η - π (sn.lookahead η)
        let ξn := curvatureError (↑P) π f η ρ x₁ n
        let un1 := auxVar P μ_minus π f η ρ x₁ (n + 1)
        let wn := un1 - Real.sqrt μ_minus • ξn
        let δ_curv := Real.sqrt μ_minus * @inner ℝ _ _ wn ξn +
                      (Real.sqrt μ_minus) ^ 2 / 2 * ‖ξn‖ ^ 2
        let a := Real.sqrt (μ_minus * η)
        let Ln := lyapunov P μ_minus π f η ρ x₁ n
        let proj_err := a * abs (@inner ℝ _ _ gn (P en))
        δ_curv + proj_err ≤ θ * a * Ln := by
      -- Curvature absorption: extracted to curv_absorb_assembly for heartbeat isolation
      suffices h_curv : ∃ R_abs : ℝ, 0 < R_abs ∧ ∀ (x₁ : E d) (n : ℕ),
          (nesterovSeq f η ρ x₁ n).x ∈ Metric.ball mstar R_abs →
          (nesterovSeq f η ρ x₁ n).lookahead η ∈ Metric.ball mstar R_abs →
          lyapunov P μ_minus π f η ρ x₁ n ≤ R_abs ^ 2 →
          let sn := nesterovSeq f η ρ x₁ n
          let gn := gradient f (sn.lookahead η)
          let en := sn.lookahead η - π (sn.lookahead η)
          let ξn := curvatureError (↑P) π f η ρ x₁ n
          let un1 := auxVar P μ_minus π f η ρ x₁ (n + 1)
          let wn := un1 - Real.sqrt μ_minus • ξn
          let δ_curv := Real.sqrt μ_minus * @inner ℝ _ _ wn ξn +
                        (Real.sqrt μ_minus) ^ 2 / 2 * ‖ξn‖ ^ 2
          let a := Real.sqrt (μ_minus * η)
          let Ln := lyapunov P μ_minus π f η ρ x₁ n
          let proj_err := a * abs (@inner ℝ _ _ gn (P en))
          δ_curv + proj_err ≤ θ * a * Ln from h_curv
      have hπ_diff_near : ∃ δ_diff > 0,
          ∀ z ∈ Metric.ball mstar δ_diff, DifferentiableAt ℝ π z := by
        -- ContDiffAt (n+1) gives HasFDerivAt in a neighborhood
        have hfda := (contDiffAt_succ_iff_hasFDerivAt (n := 0)).mp
          (by exact_mod_cast hπ'_C1 mstar hmstar)
        obtain ⟨f', ⟨u, hu_nhds, hf'_u⟩, _⟩ := hfda
        -- Extract ball from u ∈ 𝓝 mstar
        obtain ⟨δ₁, hδ₁_pos, hδ₁_sub⟩ := Metric.mem_nhds_iff.mp hu_nhds
        -- Extract ball from U ∈ 𝓝 mstar
        obtain ⟨δ₂, hδ₂_pos, hδ₂_sub⟩ :=
          Metric.isOpen_iff.mp hTub_sub.isOpen mstar (hTub_sub.subset hmstar)
        refine ⟨min δ₁ δ₂, lt_min hδ₁_pos hδ₂_pos, fun z hz => ?_⟩
        have hdz := Metric.mem_ball.mp hz
        have hz_u : z ∈ u := hδ₁_sub (lt_of_lt_of_le hdz (min_le_left _ _))
        have hz_U : z ∈ U :=
          hδ₂_sub (Metric.mem_ball.mpr (lt_of_lt_of_le hdz (min_le_right _ _)))
        have hπ'_diff : DifferentiableAt ℝ π' z := (hf'_u z hz_u).differentiableAt
        have h_evt_z : π =ᶠ[𝓝 z] π' :=
          (hTub_sub.isOpen.eventually_mem hz_U).mono (fun y hy => hπ_eq_on_U' y hy)
        exact h_evt_z.differentiableAt_iff.mpr hπ'_diff
      exact curv_absorb_assembly f L hL μ_minus hμ_minus θ hθ η ρ hη_pos hμη_lt1_pre rfl
        S π P hP_ortho mstar hmstar rfl U_plus hU_open hm_in
        U hTub_sub.isOpen hU_sub
        hf_lip (hTub_sub.subset) (hTub_sub.subset hmstar)
        hπ_on_U
        hDπ_cont C_coer hC_coer
        (fun x₁ n h1 h2 => (hcoer_bound x₁ n h1 h2).1)
        hπ_kills_normal hgrad_zero hπ_diff_near
    obtain ⟨R_abs, hR_abs_pos, h_curv_absorb_hyp⟩ := h_curv_absorb_hyp
    -- Segment estimate hypothesis (from C² + Hessian bound)
    have hSegment_hyp : ∀ x z : E d, x ∈ U_plus → z ∈ U_plus →
        (∀ t : ℝ, 0 ≤ t → t ≤ 1 → (1 - t) • z + t • x ∈ U_plus) →
        @inner ℝ _ _ (gradient f x) (x - z) ≥
          f x - f z - ε / 2 * ‖x - z‖ ^ 2 := by
      intro x z hxU hzU hseg
      set ξ := x - z with hξ_def
      set φ : ℝ → ℝ := fun t => f (z + t • ξ) with hφ_def
      have hφ0 : φ 0 = f z := by simp only [hφ_def, zero_smul, add_zero]
      have hφ1 : φ 1 = f x := by
        simp only [hφ_def, one_smul, hξ_def]; congr 1; abel
      have hpath : ∀ t, HasDerivAt (fun (s : ℝ) => z + s • ξ) ξ t := by
        intro t
        have h := ((hasDerivAt_id t).smul_const ξ).const_add z
        simpa [one_smul] using h
      have hseg' : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → z + t • ξ ∈ U_plus := by
        intro t ht0 ht1
        have : z + t • ξ = (1 - t) • z + t • x := by
          simp only [smul_sub, sub_smul, one_smul, ξ]; abel
        rw [this]; exact hseg t ht0 ht1
      have hφ_hd : ∀ t, 0 ≤ t → t ≤ 1 →
          HasDerivAt φ (fderiv ℝ f (z + t • ξ) ξ) t := by
        intro t ht0 ht1
        have hpt_Up : z + t • ξ ∈ U_plus := hseg' t ht0 ht1
        have hda : DifferentiableAt ℝ f (z + t • ξ) :=
          hf_diffOn_Up.differentiableAt (hU_open.mem_nhds hpt_Up)
        exact hda.hasFDerivAt.comp_hasDerivAt t (hpath t)
      have hderiv1 : deriv φ 1 = @inner ℝ _ _ (gradient f x) ξ := by
        rw [(hφ_hd 1 zero_le_one le_rfl).deriv]
        have hone : z + (1 : ℝ) • ξ = x := by
          simp only [one_smul, hξ_def]; abel
        rw [hone]
        exact (inner_gradient_left (𝕜 := ℝ) (f := f) (x := x) (y := ξ)).symm
      have hφ''_eq : ∀ t, 0 ≤ t → t ≤ 1 →
          deriv (deriv φ) t = hessianQuadForm f (z + t • ξ) ξ := by
        intro t ht0 ht1
        have hpt_Up : z + t • ξ ∈ U_plus := hseg' t ht0 ht1
        have hpt_U : z + t • ξ ∈ U := hU_sub (subset_closure hpt_Up)
        have hC2at : ContDiffAt ℝ 2 f (z + t • ξ) :=
          hf_C2.contDiffAt (hTub_sub.isOpen.mem_nhds hpt_U)
        exact fiber_path_second_deriv f z ξ t hC2at
      have hφ''_lower : ∀ t, 0 ≤ t → t ≤ 1 →
          deriv (deriv φ) t ≥ -ε * ‖ξ‖ ^ 2 := by
        intro t ht0 ht1
        rw [hφ''_eq t ht0 ht1]
        exact hHessLow (z + t • ξ) (hseg' t ht0 ht1) ξ
      -- Derive local regularity from ContDiffAt ℝ 2 at each point of [0,1]
      have hφ_C2at : ∀ t ∈ Set.Icc (0:ℝ) 1, ContDiffAt ℝ 2 φ t := by
        intro t ht
        exact fiber_path_C2at_on_segment f z ξ hTub_sub.isOpen hf_C2
          (fun s hs => hU_sub (subset_closure (hseg' s hs.1 hs.2))) t ht
      have hφ_cont : ContinuousOn φ (Set.Icc 0 1) :=
        fun t ht => (hφ_C2at t ht).continuousAt.continuousWithinAt
      have hφ_diffon : DifferentiableOn ℝ φ (Set.Ioo 0 1) :=
        fun t ht => ((hφ_C2at t (Set.Ioo_subset_Icc_self ht)).differentiableAt
          (by decide : (2 : WithTop ℕ∞) ≠ 0)).differentiableWithinAt
      have hφ'_cont : ContinuousOn (deriv φ) (Set.Icc 0 1) := by
        intro t ht
        have hfda := (hφ_C2at t ht).fderiv_right
          (show (1 : WithTop ℕ∞) + 1 ≤ 2 by decide)
        have h_eq : deriv φ = fun s => fderiv ℝ φ s 1 := by
          ext s; exact fderiv_apply_one_eq_deriv.symm
        rw [h_eq]
        exact (hfda.continuousAt.clm_apply continuousAt_const).continuousWithinAt
      have hφ'_diffon : DifferentiableOn ℝ (deriv φ) (Set.Ioo 0 1) := by
        intro t ht
        have hfda := (hφ_C2at t (Set.Ioo_subset_Icc_self ht)).fderiv_right
          (show (1 : WithTop ℕ∞) + 1 ≤ 2 by decide)
        have hfda_diff := hfda.differentiableAt
          (show (1 : WithTop ℕ∞) ≠ 0 by decide)
        have h_eq : deriv φ = fun s => fderiv ℝ φ s 1 := by
          ext s; exact fderiv_apply_one_eq_deriv.symm
        rw [h_eq]
        exact (hfda_diff.clm_apply (differentiableAt_const _)).differentiableWithinAt
      have hest := segment_estimate_from_hessian φ (-ε * ‖ξ‖ ^ 2)
        hφ_cont hφ_diffon hφ'_cont hφ'_diffon hφ''_lower
      rw [hderiv1, hφ1, hφ0] at hest
      linarith
    obtain ⟨Ω, _Ω_plus, R, hΩ_open, _, hR_pos, hm_in_Ω,
            hΩ_sub_Ωp, hΩp_sub_Up, hLC⟩ :=
      lyapunov_contraction hd f L hL μ_minus hμ' θ hθ hθ_lt1 η rfl hη_pos
        ρ rfl S hS_argmin π hπ_in_S hπ_fix hgrad_zero
        P mstar hmstar ε hε_pos hε_bound hμη_lt1
        U_plus hU_open hm_in
        hf_diffOn_Up hf_lip_Up
        hStrAim hHessLow hπ_kills_normal
        hP_self_adj hP_idem
        hSegment_hyp R_abs hR_abs_pos h_curv_absorb_hyp
    have hΩ_sub_Up : Ω ⊆ U_plus := hΩ_sub_Ωp.trans hΩp_sub_Up
    have hΩ_sub_U' : Ω ⊆ U := hΩ_sub_Up.trans (subset_closure.trans hU_sub)
    refine ⟨Ω, R, hΩ_open, hR_pos, hm_in_Ω, hΩ_sub_U', hΩ_sub_Up, ?_⟩
    intro x₁ n_step _s _a hx_in hx'_in hLn_bound
    exact (hLC x₁ n_step hx_in hx'_in hLn_bound).1
  obtain ⟨Ω, R, hΩ_open, hR, hm_in_Ω, hΩ_sub_U, hΩ_sub_Uplus, hcontract⟩ := hlem4
  -- ── bootstrap_total_displacement ───────────────────────────────
  -- ∃ α > 0 such that for x₁ ∈ B(m⋆, α):
  --   (1) all iterates stay in Ω
  --   (2) all iterates remain in U
  --   (3) L_n ≤ (1−a)^n · L_0
  have hlem5 : ∃ (α : ℝ), 0 < α ∧ Metric.ball mstar α ⊆ U ∧
      ∀ x₁ ∈ Metric.ball mstar α,
        (∀ n, (nesterovSeq f η ρ x₁ n).x ∈ Ω ∧
              (nesterovSeq f η ρ x₁ n).lookahead η ∈ Ω) ∧
        (∀ n, (nesterovSeq f η ρ x₁ n).x ∈ U) ∧
        (∀ n, let a := Real.sqrt (μ_minus * η)
              lyapunov P μ_minus π f η ρ x₁ (n + 1) ≤
                (1 - (1 - θ) * a) ^ (n + 1) *
                lyapunov P μ_minus π f η ρ x₁ 0) := by
    -- ── Derive prerequisites for bootstrap_total_displacement ──
    -- (i) hπ_metric: dist x (π x) = infDist x S for x ∈ U
    have hπ_metric : ∀ x ∈ U, dist x (π x) = Metric.infDist x S :=
      fun x hx => (hπ_on_U x hx).2
    -- (ii) hπ_in_S already in scope from π definition
    -- (iii) Positivity and identities
    have hη_pos : 0 < η := one_div_pos.mpr hL
    have hη_eq : η = 1 / (↑L : ℝ) := rfl
    have hρ_eq : ρ = (1 - Real.sqrt (μ_minus * η)) /
                     (1 + Real.sqrt (μ_minus * η)) := rfl
    -- (iv) μ_minus · η < 1
    have hμη_lt1 : μ_minus * η < 1 := by
      exact hμη_lt1_pre
    -- (v) Ψ continuity and vanishing
    have hΨ_cont : ContinuousAt (psi f μ_minus S) mstar := by
      unfold psi fStar
      apply ContinuousAt.add
      · apply ContinuousAt.sub
        · exact hf_C2.continuousOn.continuousAt
            (hTub_sub.isOpen.mem_nhds (hTub_sub.subset hmstar))
        · exact continuousAt_const
      · apply ContinuousAt.mul
        · exact continuousAt_const
        · exact (Metric.continuous_infDist_pt S).continuousAt.pow 2
    have hΨ_zero : psi f μ_minus S mstar = 0 := by
      unfold psi fStar
      have hmin : ∀ y, f mstar ≤ f y := by
        have hmem : mstar ∈ argminSet f := by rwa [← hS_argmin]
        exact hmem
      have hf_eq : f mstar = iInf f :=
        le_antisymm (le_ciInf hmin)
          (ciInf_le ⟨f mstar, by rintro _ ⟨x, rfl⟩; exact hmin x⟩ mstar)
      have hdist_zero : Metric.infDist mstar S = 0 :=
        Metric.infDist_zero_of_mem hmstar
      rw [hf_eq, sub_self, hdist_zero]; ring
    -- (vi) QG on Ω from QG on U_plus
    have hQG_Ω : ∀ x ∈ Ω,
        f x - fStar f ≥ μ_minus / 2 * (Metric.infDist x S) ^ 2 :=
      fun x hx => hQG x (hΩ_sub_Uplus hx)
    -- (vii) Weaken contraction: (1-a)·Ln ≤ (1-(1-θ)·a)·Ln
    have hcontract_weak : ∀ (x₁ : E d) (n : ℕ),
        let s := nesterovSeq f η ρ x₁ n
        let Ln := lyapunov P μ_minus π f η ρ x₁ n
        let Ln' := lyapunov P μ_minus π f η ρ x₁ (n + 1)
        let a := Real.sqrt (μ_minus * η)
        s.x ∈ Ω → s.lookahead η ∈ Ω → Ln ≤ R ^ 2 →
        Ln' ≤ (1 - (1 - θ) * a) * Ln := by
      intro x₁ n_val _s _Ln _Ln' _a hsx hslx hLn_le
      have hstr := hcontract x₁ n_val hsx hslx hLn_le
      -- Ln ≥ 0
      have hmstar_argmin : mstar ∈ argminSet f := by rwa [← hS_argmin]
      have hmin_val : ∀ y, f mstar ≤ f y := hmstar_argmin
      have hbdd : BddBelow (Set.range f) :=
        ⟨f mstar, by rintro _ ⟨x, rfl⟩; exact hmin_val x⟩
      have hLn_nn : 0 ≤ lyapunov P μ_minus π f η ρ x₁ n_val := by
        unfold lyapunov
        have hgap : 0 ≤ f (nesterovSeq f η ρ x₁ n_val).x - fStar f :=
          sub_nonneg.mpr (ciInf_le hbdd _)
        have hu2 : 0 ≤ ‖auxVar P μ_minus π f η ρ x₁ n_val‖ ^ 2 / 2 :=
          div_nonneg (sq_nonneg _) two_pos.le
        have ha_lt1 : Real.sqrt (μ_minus * η) < 1 := by
          rw [← Real.sqrt_one]
          exact Real.sqrt_lt_sqrt
            (le_of_lt (mul_pos (by linarith : (0:ℝ) < μ_minus) hη_pos))
            hμη_lt1
        have hlam : 0 ≤ (1 + Real.sqrt (μ_minus * η)) ^ 2 /
            (2 * (1 - Real.sqrt (μ_minus * η))) :=
          le_of_lt (div_pos (by positivity) (by linarith))
        have h_Pv_sq := sq_nonneg ‖P (nesterovSeq f η ρ x₁ n_val).v‖
        have h_lam_Pv := mul_nonneg hlam h_Pv_sq
        linarith
      exact hstr
    -- (viii) Motion bounds from motion_bounds_curvature_error
    have hmotion : ∃ (C_h : ℝ) (_ : 0 < C_h)
        (hstep_bound : ∀ (x₁ : E d) (n : ℕ),
          let s := nesterovSeq f η ρ x₁ n
          let Ln := lyapunov P μ_minus π f η ρ x₁ n
          s.x ∈ Ω → s.lookahead η ∈ Ω → Ln ≤ R ^ 2 →
          ‖nesterovH f η ρ x₁ n‖ ≤ C_h * Real.sqrt η * Real.sqrt Ln)
        (C_mov : ℝ) (_ : 0 < C_mov),
        ∀ (x₁ : E d) (n : ℕ),
          let s := nesterovSeq f η ρ x₁ n
          let s' := nesterovSeq f η ρ x₁ (n + 1)
          let Ln := lyapunov P μ_minus π f η ρ x₁ n
          s.x ∈ Ω → s.lookahead η ∈ Ω → Ln ≤ R ^ 2 →
          ‖Real.sqrt η • s'.v‖ ≤ C_mov * Real.sqrt Ln := by
      -- Setup
      have hη_pos_local : 0 < η := one_div_pos.mpr hL
      have hη_nn : (0 : ℝ) ≤ η := le_of_lt hη_pos_local
      have hsqrt_η_nn : (0 : ℝ) ≤ Real.sqrt η := Real.sqrt_nonneg η
      have hL_nn : (0 : ℝ) ≤ (↑L : ℝ) := le_of_lt hL
      have hC_coer_nn : (0 : ℝ) ≤ C_coer := le_of_lt hC_coer
      have hmu4_pos : (0 : ℝ) < μ_minus := by linarith
      -- Constants
      let K := C_coer / μ_minus
      let Ce := Real.sqrt K
      let Cg := (↑L : ℝ) * Ce
      let Cv := Real.sqrt C_coer
      let Cv' := |ρ| * (Cv + Real.sqrt η * Cg)
      let Ch := Cv' + Real.sqrt η * Cg + 1
      let Cmov := Real.sqrt η * Cv' + 1
      -- Combined bounds helper
      have hbounds : ∀ (x₁ : E d) (n_step : ℕ),
          (nesterovSeq f η ρ x₁ n_step).x ∈ Ω →
          (nesterovSeq f η ρ x₁ n_step).lookahead η ∈ Ω →
          ‖nesterovH f η ρ x₁ n_step‖ ≤ Ch * Real.sqrt η *
            Real.sqrt (lyapunov P μ_minus π f η ρ x₁ n_step) ∧
          ‖Real.sqrt η • (nesterovSeq f η ρ x₁ (n_step + 1)).v‖ ≤
            Cmov * Real.sqrt (lyapunov P μ_minus π f η ρ x₁ n_step) := by
        intro x₁ n_step hsx hslx
        set Ln := lyapunov P μ_minus π f η ρ x₁ n_step
        set s := nesterovSeq f η ρ x₁ n_step
        set s' := nesterovSeq f η ρ x₁ (n_step + 1)
        set gn := nesterovGrad f η ρ x₁ n_step
        set en := normalDisp π f η ρ x₁ n_step
        -- Coercivity
        have hcoer_here := (hcoer_bound x₁ n_step
          (hΩ_sub_Uplus hsx) (hΩ_sub_Uplus hslx)).1
        -- Ln ≥ 0
        have hLn_nn : 0 ≤ Ln := by
          have h1 : 0 ≤ ‖s.v‖ ^ 2 + μ_minus * ‖en‖ ^ 2 :=
            add_nonneg (sq_nonneg _) (mul_nonneg (le_of_lt hmu4_pos) (sq_nonneg _))
          nlinarith [hcoer_here]
        -- (1) ‖s.v‖ ≤ Cv * √Ln
        have hv_sq : ‖s.v‖ ^ 2 ≤ C_coer * Ln := by
          have : 0 ≤ μ_minus * ‖en‖ ^ 2 :=
            mul_nonneg (le_of_lt hmu4_pos) (sq_nonneg _)
          linarith [hcoer_here]
        have hv_bound : ‖s.v‖ ≤ Cv * Real.sqrt Ln := by
          rw [show Cv = Real.sqrt C_coer from rfl,
              ← Real.sqrt_mul hC_coer_nn,
              ← Real.sqrt_sq (norm_nonneg s.v)]
          exact Real.sqrt_le_sqrt hv_sq
        -- (2) ‖en‖ ≤ Ce * √Ln
        have he_sq : ‖en‖ ^ 2 ≤ K * Ln := by
          have h1 : μ_minus * ‖en‖ ^ 2 ≤ C_coer * Ln := by
            have := sq_nonneg ‖s.v‖
            linarith [hcoer_here]
          have hKmu : μ_minus * K = C_coer := by
            change μ_minus * (C_coer / μ_minus) = C_coer
            field_simp
          have h2 : μ_minus * (K * Ln) = C_coer * Ln := by
            rw [← hKmu]; ring
          by_contra h; push Not at h
          linarith [mul_lt_mul_of_pos_left h hmu4_pos]
        have he_bound : ‖en‖ ≤ Ce * Real.sqrt Ln := by
          have hK_nn : (0 : ℝ) ≤ K := by positivity
          rw [show Ce = Real.sqrt K from rfl,
              ← Real.sqrt_mul hK_nn,
              ← Real.sqrt_sq (norm_nonneg en)]
          exact Real.sqrt_le_sqrt he_sq
        -- (3) ‖gn‖ ≤ ↑L * ‖en‖ ≤ Cg * √Ln
        have hg_raw : ‖gn‖ ≤ (↑L : ℝ) * ‖en‖ := by
          change ‖gradient f ((nesterovSeq f η ρ x₁ n_step).lookahead η)‖ ≤
            (↑L : ℝ) * ‖(nesterovSeq f η ρ x₁ n_step).lookahead η -
              π ((nesterovSeq f η ρ x₁ n_step).lookahead η)‖
          exact gradient_bound_from_lipschitz f L hf_lip _ _
            (hΩ_sub_U hslx)
            (hTub_sub.subset (hπ_in_S _))
            (hgrad_zero _ (hπ_in_S _))
        have hg_bound : ‖gn‖ ≤ Cg * Real.sqrt Ln := by
          calc ‖gn‖ ≤ (↑L : ℝ) * ‖en‖ := hg_raw
            _ ≤ (↑L : ℝ) * (Ce * Real.sqrt Ln) := by
                apply mul_le_mul_of_nonneg_left he_bound hL_nn
            _ = Cg * Real.sqrt Ln := by ring
        -- (4) s'.v = ρ • (s.v - √η • gn) [velocity identity]
        have hv'_eq : s'.v = ρ • (s.v - Real.sqrt η • gn) := by
          change (nesterovSeq f η ρ x₁ (n_step + 1)).v =
            ρ • ((nesterovSeq f η ρ x₁ n_step).v -
              Real.sqrt η • nesterovGrad f η ρ x₁ n_step)
          simp only [nesterovSeq, nesterovStep, nesterovGrad,
            NesterovState.lookahead]
        -- (5) ‖s'.v‖ ≤ Cv' * √Ln
        have hv'_bound : ‖s'.v‖ ≤ Cv' * Real.sqrt Ln := by
          have hv'_norm : ‖s'.v‖ ≤ |ρ| * (‖s.v‖ + |Real.sqrt η| * ‖gn‖) := by
            rw [hv'_eq]
            exact velocity_bound_from_step s.v gn ρ (Real.sqrt η)
          rw [abs_of_nonneg hsqrt_η_nn] at hv'_norm
          calc ‖s'.v‖
              ≤ |ρ| * (‖s.v‖ + Real.sqrt η * ‖gn‖) := hv'_norm
            _ ≤ |ρ| * (Cv * Real.sqrt Ln +
                  Real.sqrt η * (Cg * Real.sqrt Ln)) := by
                apply mul_le_mul_of_nonneg_left _ (abs_nonneg ρ)
                linarith [hv_bound, hg_bound,
                  mul_le_mul_of_nonneg_left hg_bound hsqrt_η_nn]
            _ = Cv' * Real.sqrt Ln := by ring
        -- (6) nesterovH decomposition: hn = √η • s'.v - η • gn
        have hhn_eq : nesterovH f η ρ x₁ n_step =
            Real.sqrt η • s'.v - η • gn := by
          change (nesterovSeq f η ρ x₁ (n_step + 1)).x +
              Real.sqrt η • (nesterovSeq f η ρ x₁ (n_step + 1)).v -
              ((nesterovSeq f η ρ x₁ n_step).x +
                Real.sqrt η • (nesterovSeq f η ρ x₁ n_step).v) =
            Real.sqrt η • (nesterovSeq f η ρ x₁ (n_step + 1)).v -
              η • nesterovGrad f η ρ x₁ n_step
          simp only [nesterovSeq, nesterovStep, nesterovGrad,
            NesterovState.lookahead]
          abel
        -- (7) Prove both bounds
        constructor
        · -- Step bound: ‖hn‖ ≤ Ch * √η * √Ln
          have hstep_raw : ‖nesterovH f η ρ x₁ n_step‖ ≤
              |Real.sqrt η| * ‖s'.v‖ + |η| * ‖gn‖ := by
            rw [hhn_eq]
            exact step_bound s'.v gn (Real.sqrt η) η
          rw [abs_of_nonneg hsqrt_η_nn, abs_of_nonneg hη_nn] at hstep_raw
          have hsqrt_Ln_nn := Real.sqrt_nonneg Ln
          calc ‖nesterovH f η ρ x₁ n_step‖
              ≤ Real.sqrt η * ‖s'.v‖ + η * ‖gn‖ := hstep_raw
            _ ≤ Real.sqrt η * (Cv' * Real.sqrt Ln) +
                  η * (Cg * Real.sqrt Ln) := by
                linarith [mul_le_mul_of_nonneg_left hv'_bound hsqrt_η_nn,
                          mul_le_mul_of_nonneg_left hg_bound hη_nn]
            _ = (Cv' + Real.sqrt η * Cg) * Real.sqrt η * Real.sqrt Ln := by
                have hη_sq := (Real.mul_self_sqrt hη_nn).symm
                linear_combination Cg * Real.sqrt Ln * hη_sq
            _ ≤ Ch * Real.sqrt η * Real.sqrt Ln := by
                have : 0 ≤ 1 * (Real.sqrt η * Real.sqrt Ln) :=
                  mul_nonneg one_pos.le (mul_nonneg hsqrt_η_nn hsqrt_Ln_nn)
                change (Cv' + Real.sqrt η * Cg) * Real.sqrt η * Real.sqrt Ln ≤
                  (Cv' + Real.sqrt η * Cg + 1) * Real.sqrt η * Real.sqrt Ln
                linarith
        · -- Velocity bound: ‖√η • s'.v‖ ≤ Cmov * √Ln
          have hsqrt_Ln_nn := Real.sqrt_nonneg Ln
          calc ‖Real.sqrt η • s'.v‖
              = Real.sqrt η * ‖s'.v‖ := by
                rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hsqrt_η_nn]
            _ ≤ Real.sqrt η * (Cv' * Real.sqrt Ln) := by
                exact mul_le_mul_of_nonneg_left hv'_bound hsqrt_η_nn
            _ = (Real.sqrt η * Cv') * Real.sqrt Ln := by ring
            _ ≤ Cmov * Real.sqrt Ln := by
                have : 0 ≤ 1 * Real.sqrt Ln := mul_nonneg one_pos.le hsqrt_Ln_nn
                change (Real.sqrt η * Cv') * Real.sqrt Ln ≤
                  (Real.sqrt η * Cv' + 1) * Real.sqrt Ln
                linarith
      -- Provide existential witnesses
      refine ⟨Ch, by positivity, ?_, Cmov, by positivity, ?_⟩
      · intro x₁ n_step _s _Ln hsx hslx _hLn_le
        exact (hbounds x₁ n_step hsx hslx).1
      · intro x₁ n_step _s _s' _Ln hsx hslx _hLn_le
        exact (hbounds x₁ n_step hsx hslx).2
    obtain ⟨C_h, hC_h, hstep_bound, C_mov, hC_mov, hvel_bound⟩ := hmotion
    -- ── Apply bootstrap_total_displacement ──
    obtain ⟨α_boot, hα_boot, hboot_raw⟩ :=
      bootstrap_total_displacement hd f L hL μ_minus hμ' θ hθ hθ_lt1 η hη_eq hη_pos
        hμη_lt1 ρ hρ_eq S hS_argmin U hTub_sub π hπ_in_S hπ_fix hπ_metric
        P Ω hΩ_open hΩ_sub_U R hR mstar hmstar hm_in_Ω
        hΨ_cont hΨ_zero hQG_Ω hcontract_weak
        C_h hC_h hstep_bound C_mov hC_mov hvel_bound
    -- ── Shrink α so that B(m⋆, α) ⊆ Ω ⊆ U ──
    obtain ⟨r_Ω, hr_Ω_pos, hball_Ω⟩ :=
      Metric.isOpen_iff.mp hΩ_open mstar hm_in_Ω
    refine ⟨min α_boot r_Ω, lt_min hα_boot hr_Ω_pos, ?_, ?_⟩
    · -- B(m⋆, min α_boot r_Ω) ⊆ B(m⋆, r_Ω) ⊆ Ω ⊆ U
      exact (Metric.ball_subset_ball (min_le_right _ _)).trans
        (hball_Ω.trans hΩ_sub_U)
    · intro x₁ hx₁
      have hx₁_boot : x₁ ∈ Metric.ball mstar α_boot :=
        Metric.ball_subset_ball (min_le_left _ _) hx₁
      have hx₁_U : x₁ ∈ U :=
        hΩ_sub_U (hball_Ω (Metric.ball_subset_ball (min_le_right _ _) hx₁))
      obtain ⟨hstay_Ω', hstay_U', hdecay_weak⟩ :=
        hboot_raw x₁ ⟨hx₁_boot, hx₁_U⟩
      refine ⟨hstay_Ω', hstay_U', ?_⟩
      -- Geometric decay from bootstrap with (1-(1-θ)·a)^{n+1}·L₀.
      intro n
      exact hdecay_weak n
  obtain ⟨α, hα_pos, hball_sub, hboot⟩ := hlem5
  -- ── Assemble the local result ──
  refine ⟨α, hα_pos, hball_sub, ?_⟩
  intro x₁ hx₁
  obtain ⟨hstay_Ω, hstay_U, hdecay⟩ := hboot x₁ hx₁
  constructor
  · -- All lookahead iterates stay in U.
    -- x_n ∈ U by hstay_U, and x'_n = x_n + √η·v_n.
    -- ‖√η·v_n‖ ≤ √(η·C_coer·L_n) → 0 as n → ∞, so x'_n ∈ U for
    -- small enough initial L_0 (guaranteed by α choice).
    intro k; exact hΩ_sub_U (hstay_Ω k).2
  · -- HasAcceleratedRate: f(x'_k) − f⋆ ≤ C · exp(−k/√(L/μ_minus))
    -- From Lyapunov decay: L_k ≤ (1−a)^k · L_0
    -- f(x'_k) − f⋆ ≤ C_f · L_k (by L-smoothness + coercivity)
    -- (1−a)^k ≤ exp(−ka) = exp(−k/√(L/μ_minus))  (by 1−x ≤ exp(−x))
    -- Extend Lyapunov decay to all k (k=0 is trivial)
    have hlyap_all : ∀ k, lyapunov P μ_minus π f η ρ x₁ k ≤
        (1 - (1 - θ) * Real.sqrt (μ_minus * η)) ^ k * lyapunov P μ_minus π f η ρ x₁ 0 := by
      intro k; cases k with
      | zero => simp only [pow_zero, one_mul, le_refl]
      | succ n => exact hdecay n
    have ha_le1 : Real.sqrt (μ_minus * η) ≤ 1 := by
      rw [← Real.sqrt_one]; apply Real.sqrt_le_sqrt
      rw [show η = 1 / (↑L : ℝ) from rfl, mul_one_div, div_le_one hL]
      linarith [hmu4_le_L]
    have hb_le1 : (1 - θ) * Real.sqrt (μ_minus * η) ≤ 1 := by
      have := Real.sqrt_le_sqrt
        (show μ_minus * η ≤ 1 by
          rw [show η = 1 / (↑L : ℝ) from rfl, mul_one_div, div_le_one hL]
          linarith [hmu4_le_L])
      rw [Real.sqrt_one] at this
      have h1mθ : 1 - θ ≤ 1 := by linarith [hθ_lt1]
      have hsqrt_nn : (0 : ℝ) ≤ Real.sqrt (μ_minus * η) := Real.sqrt_nonneg _
      have := mul_le_mul_of_nonneg_right h1mθ hsqrt_nn
      linarith
    -- f(x'_k) − f⋆ bounded by constant times Lyapunov
    -- (by L-smoothness: f(x') ≤ f(x) + ⟨∇f(x), √η·v⟩ + (L/2)·η·‖v‖²,
    --  coercivity: ‖v‖² ≤ C_coer · L_k, gradient Lipschitz: ‖∇f(x)‖ ≤ L·dist(x,S))
    have hf_le : ∃ Cf : ℝ, 0 < Cf ∧ ∀ k,
        f ((nesterovSeq f η ρ x₁ k).lookahead η) - fStar f ≤
          Cf * lyapunov P μ_minus π f η ρ x₁ k := by
      /-
        f(x'ₖ) − f⋆ = (f(xₖ) − f⋆) + (f(x'ₖ) − f(xₖ)).
        • Gap  f(xₖ) − f⋆  is a summand of the Lyapunov Lₖ.
        • By L-smooth upper bound  f(x'ₖ) − f(xₖ) ≤ O(‖vₖ‖²).
        • By coercivity  ‖vₖ‖² ≤ C_coer · Lₖ.
        Uses the L-smooth quadratic upper bound (lsmooth_descent_at)
        and Ω ⊆ U_plus neighborhood matching (hlem2).
      -/
      have hmin : ∀ y, f mstar ≤ f y := by
        have : mstar ∈ argminSet f := by rw [← hS_argmin]; exact hmstar
        exact this
      have hbdd : BddBelow (Set.range f) :=
        ⟨f mstar, by rintro _ ⟨x, rfl⟩; exact hmin x⟩
      refine ⟨1 + ↑L * C_coer / (2 * μ_minus), by positivity, fun k => ?_⟩
      have hlyap0_eq : lyapunov P μ_minus π f η ρ x₁ 0 =
          f x₁ - fStar f + ‖Real.sqrt μ_minus • (x₁ - π x₁)‖ ^ 2 / 2 := by
        simp only [lyapunov, nesterovSeq, auxVar, normalDisp,
          NesterovState.lookahead, map_zero, smul_zero, sub_self,
          zero_add, add_zero, norm_zero]; ring
      cases k with
      | zero =>
        simp only [nesterovSeq, NesterovState.lookahead, smul_zero, add_zero]
        have h_gap_le : f x₁ - fStar f ≤ lyapunov P μ_minus π f η ρ x₁ 0 := by
          rw [hlyap0_eq]; linarith [sq_nonneg ‖Real.sqrt μ_minus • (x₁ - π x₁)‖]
        have h_lyap_nn : 0 ≤ lyapunov P μ_minus π f η ρ x₁ 0 :=
          le_trans (sub_nonneg.mpr (ciInf_le hbdd x₁)) h_gap_le
        have hClyap := mul_nonneg
          (show (0:ℝ) ≤ ↑L * C_coer / (2 * μ_minus) by positivity) h_lyap_nn
        have hexpand :
            (1 + ↑L * C_coer / (2 * μ_minus)) * lyapunov P μ_minus π f η ρ x₁ 0 =
            lyapunov P μ_minus π f η ρ x₁ 0 +
            ↑L * C_coer / (2 * μ_minus) *
            lyapunov P μ_minus π f η ρ x₁ 0 := by ring
        linarith
      | succ n =>
        -- Direct bound via fiber QUB from π(x'_k) to x'_k
        set sn := nesterovSeq f η ρ x₁ (n + 1)
        set x'n := sn.lookahead η
        set Ln := lyapunov P μ_minus π f η ρ x₁ (n + 1)
        have hx'n_U : x'n ∈ U := hΩ_sub_U (hstay_Ω (n + 1)).2
        have hx'n_Up : x'n ∈ U_plus := hΩ_sub_Uplus (hstay_Ω (n + 1)).2
        have hπx'n := hπ_on_U x'n hx'n_U
        have hπx'n_S : π x'n ∈ S := hπx'n.1
        have hπx'n_U : π x'n ∈ U := hTub_sub.subset hπx'n_S
        set en := normalDisp π f η ρ x₁ (n + 1)
        have hen_def : en = x'n - π x'n := rfl
        -- f(π(x'_k)) = fStar f
        have hf_π : f (π x'n) = fStar f := by
          have hmin : ∀ y, f (π x'n) ≤ f y := by
            have := hπx'n_S; rw [hS_argmin] at this; exact this
          exact le_antisymm (le_ciInf hmin) (ciInf_le hbdd (π x'n))
        -- Fiber segment stays in U (from local_fiberwise_geometry property (f))
        have hseg : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → π x'n + t • en ∈ U := by
          intro t ht0 ht1
          exact hfiber_U x'n hx'n_Up t ht0 ht1
        -- QUB along fiber
        have hf_diffOn_U : DifferentiableOn ℝ f U :=
          hf_C2.differentiableOn two_ne_zero
        have hQUB : f (π x'n + en) - f (π x'n) ≤
            @inner ℝ _ _ (gradient f (π x'n)) en + ↑L / 2 * ‖en‖ ^ 2 :=
          lsmooth_qub f L hTub_sub.isOpen hf_diffOn_U hf_lip
            (π x'n) en hπx'n_U hseg
        have hπ_en : π x'n + en = x'n := by rw [hen_def]; abel
        have hgrad_πx'n : gradient f (π x'n) = 0 :=
          hgrad_zero (π x'n) hπx'n_S
        rw [hπ_en, hf_π, hgrad_πx'n, inner_zero_left, zero_add] at hQUB
        -- Coercivity: μ_minus·‖en‖² ≤ C_coer · Ln
        have hxn_Up : sn.x ∈ U_plus :=
          hΩ_sub_Uplus (hstay_Ω (n + 1)).1
        have hcoer_pair := (hcoer_bound x₁ (n + 1) hxn_Up hx'n_Up).1
        have hen_sq : μ_minus * ‖en‖ ^ 2 ≤ C_coer * Ln := by
          linarith [sq_nonneg ‖sn.v‖]
        -- f x'n - fStar f ≤ (L·C_coer/(2μ_minus))·Ln
        have hfinal : f x'n - fStar f ≤ ↑L * C_coer / (2 * μ_minus) * Ln := by
          have h1 := mul_le_mul_of_nonneg_left hQUB (le_of_lt hμ_minus)
          have h2 := mul_le_mul_of_nonneg_left hen_sq
            (show (0:ℝ) ≤ ↑L by positivity)
          have hkey : μ_minus * (f x'n - fStar f) ≤ ↑L / 2 * C_coer * Ln := by
            calc μ_minus * (f x'n - fStar f)
                ≤ μ_minus * (↑L / 2 * ‖en‖ ^ 2) := h1
              _ = ↑L / 2 * (μ_minus * ‖en‖ ^ 2) := by ring
              _ ≤ ↑L / 2 * (C_coer * Ln) :=
                  mul_le_mul_of_nonneg_left hen_sq (by positivity)
              _ = ↑L / 2 * C_coer * Ln := by ring
          rw [div_mul_eq_mul_div]
          apply (le_div_iff₀ (by positivity : (0:ℝ) < 2 * μ_minus)).mpr
          have : (f x'n - fStar f) * (2 * μ_minus) = 2 * (μ_minus * (f x'n - fStar f)) := by ring
          have : ↑L * C_coer * Ln = 2 * (↑L / 2 * C_coer * Ln) := by ring
          linarith
        -- Ln ≥ 0
        have hLn_nn : 0 ≤ Ln := by
          have h_ge : 0 ≤ f sn.x - fStar f := sub_nonneg.mpr (ciInf_le hbdd _)
          have h_le : f sn.x - fStar f ≤ Ln :=
            gap_le_lyapunov_of_sqrt_le P μ_minus π f η ρ x₁ (n + 1) ha_le1
          linarith
        have hexpand : (1 + ↑L * C_coer / (2 * μ_minus)) * Ln =
            Ln + ↑L * C_coer / (2 * μ_minus) * Ln := by ring
        linarith
    obtain ⟨Cf, hCf_pos, hf_bound⟩ := hf_le
    -- Geometric decay implies exponential rate: (1−(1-θ)a)^k ≤ exp(−(1-θ)ak)
    have hgeom_exp : ∀ k : ℕ,
        (1 - (1 - θ) * Real.sqrt (μ_minus * η)) ^ k ≤
          Real.exp (-(↑k / Real.sqrt (↑L / ((1 - θ) ^ 2 * μ_minus)))) := by
      intro k
      set a := Real.sqrt (μ_minus * η) with ha_def
      set b := (1 - θ) * a with hb_def
      have hμ_pos : (0 : ℝ) < μ_minus := by linarith
      have hη_pos : 0 < η := by change 0 < 1 / (↑L : ℝ); positivity
      have h_nn : 0 ≤ μ_minus * η := le_of_lt (mul_pos hμ_pos hη_pos)
      have ha_pos : 0 < a := Real.sqrt_pos_of_pos (mul_pos hμ_pos hη_pos)
      have h1θ_pos : (0 : ℝ) < 1 - θ := sub_pos.mpr hθ_lt1
      have hb_pos : 0 < b := mul_pos h1θ_pos ha_pos
      -- (1-θ)*a ≤ 1 since (1-θ) ≤ 1 and a ≤ 1
      have ha1 : a ≤ 1 := by
        rw [ha_def, ← Real.sqrt_one]; apply Real.sqrt_le_sqrt
        change μ_minus * (1 / ↑L) ≤ 1; rw [mul_one_div, div_le_one hL]; exact hmu4_le_L
      have hb_le1 : b ≤ 1 := by
        calc b = (1 - θ) * a := rfl
          _ ≤ 1 * a := by
              apply mul_le_mul_of_nonneg_right _ (by linarith : 0 ≤ a)
              linarith [hθ_lt1]
          _ = a := one_mul _
          _ ≤ 1 := ha1
      have h1b : 0 ≤ 1 - b := by linarith
      -- Key identity: b · √(L/((1-θ)²·μ_minus)) = 1
      have hμ_target_pos : (0 : ℝ) < (1 - θ) ^ 2 * μ_minus := by positivity
      have h_sqrt_pos : 0 < Real.sqrt (↑L / ((1 - θ) ^ 2 * μ_minus)) :=
        Real.sqrt_pos_of_pos (div_pos hL hμ_target_pos)
      have h_prod : b * Real.sqrt (↑L / ((1 - θ) ^ 2 * μ_minus)) = 1 := by
        have hb_nn : (0 : ℝ) ≤ b := le_of_lt hb_pos
        have h_ratio_nn : (0 : ℝ) ≤ ↑L / ((1 - θ) ^ 2 * μ_minus) := by positivity
        -- √(b² · y) = √(b²) · √y = b · √y
        have key : b * Real.sqrt (↑L / ((1 - θ) ^ 2 * μ_minus)) =
          Real.sqrt (b ^ 2 * (↑L / ((1 - θ) ^ 2 * μ_minus))) := by
            have h := Real.sqrt_mul (sq_nonneg b) (↑L / ((1 - θ) ^ 2 * μ_minus))
            rw [Real.sqrt_sq hb_nn] at h
            exact h.symm
        rw [key]
        have hb_sq : b ^ 2 = (1 - θ) ^ 2 * (μ_minus * η) := by
          rw [hb_def, mul_pow, ha_def, Real.sq_sqrt h_nn]
        rw [hb_sq]
        have h_eta_eq : η = 1 / (↑L : ℝ) := rfl
        have h1 : (1 - θ) ^ 2 * (μ_minus * η) * (↑L / ((1 - θ) ^ 2 * μ_minus)) = 1 := by
          rw [h_eta_eq]; field_simp
        rw [h1, Real.sqrt_one]
      have h_b_eq : b = 1 / Real.sqrt (↑L / ((1 - θ) ^ 2 * μ_minus)) := by
        rw [eq_div_iff (ne_of_gt h_sqrt_pos)]; exact h_prod
      have h_exp_eq : -(↑k / Real.sqrt (↑L / ((1 - θ) ^ 2 * μ_minus))) = ↑k * (-b) := by
        rw [h_b_eq]; ring
      rw [h_exp_eq, Real.exp_nat_mul]
      exact pow_le_pow_left₀ h1b (Real.one_sub_le_exp_neg b) k
    -- Lyapunov is nonneg: sum of (f−f⋆)(≥0) + ‖u‖²/2(≥0) + λ‖Pv‖²(≥0)
    have hlyap_nonneg : 0 ≤ lyapunov P μ_minus π f η ρ x₁ 0 := by
      have hmin : ∀ y, f mstar ≤ f y := by
        have : mstar ∈ argminSet f := by rw [← hS_argmin]; exact hmstar
        exact this
      have hbdd : BddBelow (Set.range f) :=
        ⟨f mstar, by rintro _ ⟨x, rfl⟩; exact hmin x⟩
      have h1 : 0 ≤ f x₁ - fStar f := sub_nonneg.mpr (ciInf_le hbdd x₁)
      change 0 ≤ lyapunov P μ_minus π f η ρ x₁ 0
      simp only [lyapunov, nesterovSeq, auxVar, normalDisp, NesterovState.lookahead,
        map_zero, smul_zero, sub_self, zero_add, add_zero, norm_zero]
      linarith [sq_nonneg ‖Real.sqrt μ_minus • (x₁ - π x₁)‖]
    -- Assemble the exponential rate
    refine ⟨Cf * lyapunov P μ_minus π f η ρ x₁ 0 + 1, by positivity, fun k => ?_⟩
    calc f ((nesterovSeq f η ρ x₁ k).lookahead η) - fStar f
        ≤ Cf * lyapunov P μ_minus π f η ρ x₁ k := hf_bound k
      _ ≤ Cf * ((1 - (1 - θ) * Real.sqrt (μ_minus * η)) ^ k *
            lyapunov P μ_minus π f η ρ x₁ 0) :=
          mul_le_mul_of_nonneg_left (hlyap_all k) (le_of_lt hCf_pos)
      _ = Cf * lyapunov P μ_minus π f η ρ x₁ 0 *
            (1 - (1 - θ) * Real.sqrt (μ_minus * η)) ^ k := by ring
      _ ≤ Cf * lyapunov P μ_minus π f η ρ x₁ 0 *
            Real.exp (-(↑k / Real.sqrt (↑L / ((1 - θ) ^ 2 * μ_minus)))) :=
          mul_le_mul_of_nonneg_left (hgeom_exp k)
            (mul_nonneg (le_of_lt hCf_pos) hlyap_nonneg)
      _ ≤ (Cf * lyapunov P μ_minus π f η ρ x₁ 0 + 1) *
            Real.exp (-(↑k / Real.sqrt (↑L / ((1 - θ) ^ 2 * μ_minus)))) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
          linarith


/-- Public theorem wrapper for `localConvergenceAtBasePointProof`. -/
theorem local_convergence_at_base_point
    {d : ℕ} (hd : 0 < d)
    (L : ℝ≥0) (hL : 0 < (L : ℝ))
    (μ : ℝ) (hμ : 0 < μ) (hμ_le_L : μ ≤ ↑L)
    (μ_minus : ℝ) (hμ_minus : 0 < μ_minus) (hμ_minus_lt : μ_minus < μ)
    (θ : ℝ) (hθ : 0 < θ) (hθ_lt1 : θ < 1)
    (f : E d → ℝ)
    (S : Set (E d))
    (hrange : S = argminSet f)
    (U : Set (E d))
    (hTub_sub : IsTubularNeighborhoodOfSubmanifold S U)
    (hPL : PolyakLojasiewicz f μ U)
    (hf_C2 : ContDiffOn ℝ 2 f U)
    (hf_lip : LipschitzOnWith (↑L) (gradient f) U)
    (π : E d → E d)
    (hπ_on_U : ∀ x ∈ U, π x ∈ S ∧ dist x (π x) = Metric.infDist x S)
    (hπ_fix : ∀ x ∈ S, π x = x)
    (hπ_in_S : ∀ x, π x ∈ S)
    (hgrad_zero : ∀ x ∈ S, gradient f x = 0)
    (mstar : E d) (hmstar : mstar ∈ S) :
    let η := 1 / (L : ℝ)
    let ρ := (1 - Real.sqrt (μ_minus * η)) / (1 + Real.sqrt (μ_minus * η))
    ∃ (α : ℝ), 0 < α ∧
      Metric.ball mstar α ⊆ U ∧
      ∀ x₁ ∈ Metric.ball mstar α,
        (∀ k, (nesterovSeq f η ρ x₁ k).lookahead η ∈ U) ∧
        HasAcceleratedRate f
          (fun k => (nesterovSeq f η ρ x₁ k).lookahead η) (↑L) ((1 - θ) ^ 2 * μ_minus) := by
  exact localConvergenceAtBasePointProof (d := d) (hd := hd) (L := L) (hL := hL) (μ := μ) (hμ := hμ)
    (hμ_le_L := hμ_le_L) (μ_minus := μ_minus) (hμ_minus := hμ_minus) (hμ_minus_lt := hμ_minus_lt)
    (θ := θ) (hθ := hθ) (hθ_lt1 := hθ_lt1) (f := f) (S := S) (hrange := hrange) (U := U)
    (hTub_sub := hTub_sub) (hPL := hPL) (hf_C2 := hf_C2) (hf_lip := hf_lip) (π := π)
    (hπ_on_U := hπ_on_U) (hπ_fix := hπ_fix) (hπ_in_S := hπ_in_S) (hgrad_zero := hgrad_zero)
    (mstar := mstar) (hmstar := hmstar)

end PLAcceleratedNesterovLean
