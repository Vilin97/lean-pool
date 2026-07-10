/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import LeanPool.PLAcceleratedNesterovLean.Core.EmbeddedManifold
import LeanPool.PLAcceleratedNesterovLean.Convergence.LocalGeometry.Main
import LeanPool.PLAcceleratedNesterovLean.Convergence.Coercivity.Main
import LeanPool.PLAcceleratedNesterovLean.Convergence.LyapunovContraction.GenMain
import LeanPool.PLAcceleratedNesterovLean.Convergence.Bootstrap.Main
import LeanPool.PLAcceleratedNesterovLean.Convergence.MotionError.Main
import LeanPool.PLAcceleratedNesterovLean.Convergence.CurvAbsorb.Assembly
import Mathlib.Analysis.Calculus.LocalExtr.Basic


/-!
# Per-Phase Gen Convergence (State-Based Local Argument)

State-based ("gen") version of `LocalArgument.lean`. For each m⋆ ∈ M, chains
`local_fiberwise_geometry`, `lyapunov_coercivity_gen`,
`curv_absorb_assembly_gen`, `lyapunov_contraction_gen`, motion bounds, and
`bootstrap_total_displacement_gen`

to produce a ball around m⋆ where the Nesterov iterates starting from an
arbitrary initial state s₀ (not just v=0) converge geometrically.

State-based version of `LocalArgument.lean`. The conclusion provides gen bootstrap output:
∃ δ > 0, ∀ s₀ near m⋆ with small Lyapunov →
  iterates stay in Ω ∧ Lyapunov decays geometrically with `nesterovSeqGen`.
-/

noncomputable section

namespace PLAcceleratedNesterovLean

open scoped Topology NNReal
open Manifold


/-- Per-phase gen convergence at a single base point m⋆ ∈ M.

Same hypotheses as `local_convergence_at_base_point` but with a gen conclusion:
existence of a ball where any initial state s₀ with small Lyapunov value
produces iterates staying in Ω with geometric Lyapunov decay. -/
private abbrev localConvergenceAtBasePointGenProof
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
    let P := fderiv ℝ π mstar
    ∃ (Ω : Set (E d)) (δ r_ball C_coer : ℝ),
      IsOpen Ω ∧ mstar ∈ Ω ∧ Ω ⊆ U ∧ 0 < δ ∧ 0 < r_ball ∧ 0 < C_coer ∧
      Metric.ball mstar r_ball ⊆ Ω ∧
      -- Projector properties (from π ∘ π = π and the tubular neighborhood)
      (∀ x : E d, P (P x) = P x) ∧
      (∀ v : E d, ‖P v‖ ≤ ‖v‖) ∧
      -- Parameter bound (derived from μ ≤ L)
      μ_minus * η < 1 ∧
      -- Coercivity on Ω (velocity + normal displacement bounded by Lyapunov)
      (∀ s : NesterovState d, s.x ∈ Ω → s.lookahead η ∈ Ω →
        ‖s.v‖ ^ 2 + μ_minus * ‖normalDispOfState π η s‖ ^ 2 ≤
          C_coer * lyapunovOfState P μ_minus π f η s) ∧
      -- Iterate behavior
      ∀ s₀ : NesterovState d,
        s₀.x ∈ Metric.ball mstar δ →
        s₀.lookahead η ∈ Metric.ball mstar δ →
        lyapunovOfState P μ_minus π f η s₀ ≤ δ ^ 2 →
        (∀ n : ℕ,
          (nesterovSeqGen f η ρ s₀ n).x ∈ Ω ∧
          (nesterovSeqGen f η ρ s₀ n).lookahead η ∈ Ω) ∧
        (∀ n : ℕ,
          (nesterovSeqGen f η ρ s₀ n).x ∈ Metric.ball mstar r_ball ∧
          (nesterovSeqGen f η ρ s₀ n).lookahead η ∈ Metric.ball mstar r_ball) ∧
        (∀ n : ℕ,
          lyapunovOfState P μ_minus π f η (nesterovSeqGen f η ρ s₀ (n + 1)) ≤
            (1 - (1 - θ) * Real.sqrt (μ_minus * η)) ^ (n + 1) *
            lyapunovOfState P μ_minus π f η s₀) ∧
        (∀ j : ℕ, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
          π ((nesterovSeqGen f η ρ s₀ j).lookahead η) +
            t • ((nesterovSeqGen f η ρ s₀ j).lookahead η -
                  π ((nesterovSeqGen f η ρ s₀ j).lookahead η)) ∈ U) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let η := 1 / (L : ℝ)
  let ρ := (1 - Real.sqrt (μ_minus * η)) / (1 + Real.sqrt (μ_minus * η))
  have hS_argmin : S = argminSet f := hrange
  have hμ' : 0 < μ_minus := hμ_minus
  have hμ'_lt : μ_minus < μ := hμ_minus_lt
  have hη_pos : (0 : ℝ) < η := one_div_pos.mpr hL
  -- ── local_fiberwise_geometry ───────────────────────────────────
  have hlem1 : ∃ (U_plus : Set (E d)) (ε : ℝ),
      IsOpen U_plus ∧ mstar ∈ U_plus ∧ 0 < ε ∧
      ε ≤ Real.sqrt (μ_minus / η) ∧
      IsCompact (closure U_plus) ∧ closure U_plus ⊆ U ∧
      Convex ℝ U_plus ∧
      (∀ x ∈ U_plus, ∀ ξ : E d, fderiv ℝ π (π x) ξ = 0 →
        hessianQuadForm f x ξ ≥ μ_minus * ‖ξ‖ ^ 2) ∧
      (∀ x ∈ U_plus, f x - fStar f ≥ μ_minus / 2 * (Metric.infDist x S) ^ 2) ∧
      (∀ x ∈ U_plus, @inner ℝ _ _ (gradient f x) (x - π x) ≥
        f x - fStar f + μ_minus / 2 * ‖x - π x‖ ^ 2) ∧
      (∀ x ∈ U_plus, ∀ ξ : E d,
        hessianQuadForm f x ξ ≥ -ε * ‖ξ‖ ^ 2) ∧
      (∀ ξ : E d, fderiv ℝ π mstar ξ = 0 →
        hessianQuadForm f mstar ξ ≥ μ * ‖ξ‖ ^ 2) ∧
      (∀ x ∈ U_plus, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        π x + t • (x - π x) ∈ U) := by
    obtain ⟨U_plus, ε, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ :=
      local_fiberwise_geometry hd f L hL μ hμ μ_minus hμ_minus hμ_minus_lt η rfl
        (one_div_pos.mpr hL) S hS_argmin U hTub_sub hPL
        hf_C2 π hπ_on_U hgrad_zero mstar hmstar
    exact ⟨U_plus, ε, h1, h2, h6, h7, h3, h4, h5, h8, h9, h10, h11, h12, h13⟩
  obtain ⟨U_plus, ε, hU_open, hm_in, hε_pos, hε_le, hU_cpt, hU_sub,
          hU_convex, _hNormHess, hQG, hStrAim, hHessLow, _hNormHess_mu, h_seg⟩ := hlem1
  -- Derive DifferentiableOn and LipschitzOnWith on U_plus from U hypotheses
  have hf_C2_on_U : ContDiffOn ℝ 2 f U := hf_C2
  have hf_diffOn_Up : DifferentiableOn ℝ f U_plus :=
    (hf_C2.differentiableOn (by decide : (2 : WithTop ℕ∞) ≠ 0)).mono
      (subset_closure.trans hU_sub)
  have hf_lip_Up : LipschitzOnWith L (gradient f) U_plus :=
    hf_lip.mono (subset_closure.trans hU_sub)
  -- ── Define P = Dπ(m⋆), the tangent projector at the base point ──
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
  have hDπ_cont : ContinuousAt (fun x => fderiv ℝ π x) mstar := by
    have hCA_π' : ContinuousAt (fderiv ℝ π') mstar :=
      (hπ'_C1 mstar hmstar).continuousAt_fderiv one_ne_zero
    exact hCA_π'.congr (h_evt_eq'.fderiv.symm)
  have hP_self_adj : ∀ x y : E d, @inner ℝ _ _ (P x) y = @inner ℝ _ _ x (P y) := by
    intro x y
    simp only [hP_def, h_fderiv_eq']
    exact hπ'_self_adj mstar hmstar x y
  have hP_idem : ∀ x : E d, P (P x) = P x := by
    have h_pipi : ∀ x, π (π x) = π x := fun x => hπ_fix (π x) (hπ_in_S x)
    have hπ_diff : DifferentiableAt ℝ π mstar :=
      h_evt_eq'.differentiableAt_iff.mpr (hπ'_diff mstar hmstar)
    have h_eq : fderiv ℝ (fun x => π (π x)) mstar = fderiv ℝ π mstar := by
      have : (fun x => π (π x)) = π := funext h_pipi
      rw [this]
    have hπm : π mstar = mstar := hπ_fix mstar hmstar
    have h_chain : fderiv ℝ (fun x => π (π x)) mstar =
        (fderiv ℝ π mstar).comp (fderiv ℝ π mstar) := by
      have hπ_diff_at_πm : DifferentiableAt ℝ π (π mstar) := by rwa [hπm]
      have := fderiv_comp mstar hπ_diff_at_πm hπ_diff
      rwa [hπm] at this
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
  -- ── lyapunov_coercivity_gen ────────────────────────────────────
  have hπ_metric_Up : ∀ x ∈ U_plus, dist x (π x) = Metric.infDist x S := by
    intro x hx; exact (hπ_on_U x (hU_sub (subset_closure hx))).2
  have hP_ortho : ∀ v : E d, ‖v‖ ^ 2 = ‖P v‖ ^ 2 + ‖v - P v‖ ^ 2 :=
    fun v => pythagorean_proj P hP_self_adj hP_idem v
  obtain ⟨C_coer, C_Ψ, hC_coer, hC_Ψ, hcoer_bound⟩ :=
    lyapunov_coercivity_gen hd f L hL μ_minus (by linarith : (0:ℝ) < μ_minus) η rfl
      (one_div_pos.mpr hL) hμη_lt1_pre S hS_argmin π hπ_fix hπ_in_S
      P hP_idem hP_self_adj hP_ortho U_plus hπ_metric_Up hQG
  -- ── Curvature absorption (gen) ──────────────────────────────────
  -- Prerequisites
  have hε_bound : ε * η ≤ Real.sqrt (μ_minus * η) := by
    have h_nn : (0:ℝ) ≤ ε * η := mul_nonneg (le_of_lt hε_pos) (le_of_lt hη_pos)
    rw [Real.le_sqrt h_nn (mul_nonneg (by linarith : (0:ℝ) ≤ μ_minus) (le_of_lt hη_pos))]
    have hε_sq : ε ^ 2 ≤ μ_minus / η := by
      have h1 := hε_le
      have h2 := Real.sq_sqrt (div_nonneg
          (by linarith : (0:ℝ) ≤ μ_minus) (le_of_lt hη_pos))
      have h3 := sq_abs ε
      have h4 := sq_abs (Real.sqrt (μ_minus / η))
      have h5 := abs_of_nonneg (le_of_lt hε_pos)
      have h6 := abs_of_nonneg (Real.sqrt_nonneg (μ_minus / η))
      nlinarith
    have h_sq_η := sq_nonneg η
    have h_prod_sq : (ε * η) ^ 2 = ε ^ 2 * η ^ 2 := by ring
    have h_cancel : (μ_minus / η) * η ^ 2 = μ_minus * η := by field_simp
    nlinarith
  have hπ_kills_normal : ∀ x ∈ U_plus,
      fderiv ℝ π (π x) (x - π x) = 0 := by
    intro x hx
    have hxU : x ∈ U := hU_sub (subset_closure hx)
    have hπxS : π x ∈ S := (hπ_on_U x hxU).1
    have hπxU : π x ∈ U := hTub_sub.subset hπxS
    have hS_ne : S.Nonempty := ⟨mstar, hmstar⟩
    obtain ⟨π', hπ'_on_U, _, _, _, _, _, hπ'_kills, _, _, _⟩ :=
      tubular_neighborhood_projection hTub_sub hS_ne
    have hπ_eq_on_U : ∀ y ∈ U, π y = π' y := by
      intro y hyU
      have h1 := hπ_on_U y hyU
      have h2 := hπ'_on_U y hyU
      obtain ⟨_, _, huniq⟩ := hTub_sub.uniqueProj y hyU
      exact (huniq (π y) ⟨h1.1, h1.2⟩).trans
        (huniq (π' y) ⟨h2.1, by rw [dist_eq_norm]; exact h2.2⟩).symm
    have h_evt_eq : π =ᶠ[𝓝 (π x)] π' :=
      (hTub_sub.isOpen.eventually_mem hπxU).mono
        (fun y hy => hπ_eq_on_U y hy)
    have h := hπ'_kills x hxU
    rw [← hπ_eq_on_U x hxU] at h
    rwa [← h_evt_eq.fderiv_eq] at h
  have hπ_diff_near : ∃ δ_diff > 0,
      ∀ z ∈ Metric.ball mstar δ_diff, DifferentiableAt ℝ π z := by
    have hfda := (contDiffAt_succ_iff_hasFDerivAt (n := 0)).mp
      (by exact_mod_cast hπ'_C1 mstar hmstar)
    obtain ⟨f', ⟨u, hu_nhds, hf'_u⟩, _⟩ := hfda
    obtain ⟨δ₁, hδ₁_pos, hδ₁_sub⟩ := Metric.mem_nhds_iff.mp hu_nhds
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
  -- Apply curv_absorb_assembly_gen
  obtain ⟨R_abs, hR_abs_pos, h_curv_absorb_hyp⟩ :=
    curv_absorb_assembly_gen f L hL μ_minus hμ_minus θ hθ η ρ hη_pos hμη_lt1_pre rfl
      S π P hP_ortho mstar hmstar rfl U_plus hU_open hm_in
      U hTub_sub.isOpen hU_sub
      hf_lip (hTub_sub.subset) (hTub_sub.subset hmstar)
      hπ_on_U
      hDπ_cont C_coer hC_coer
      (fun s h1 h2 => (hcoer_bound s h1 h2).1)
      hπ_kills_normal hgrad_zero hπ_diff_near
  -- ── Segment estimate (identical to LocalArgument) ──────────────
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
        hf_C2_on_U.contDiffAt (hTub_sub.isOpen.mem_nhds hpt_U)
      exact fiber_path_second_deriv f z ξ t hC2at
    have hφ''_lower : ∀ t, 0 ≤ t → t ≤ 1 →
        deriv (deriv φ) t ≥ -ε * ‖ξ‖ ^ 2 := by
      intro t ht0 ht1
      rw [hφ''_eq t ht0 ht1]
      exact hHessLow (z + t • ξ) (hseg' t ht0 ht1) ξ
    have hφ_C2at : ∀ t ∈ Set.Icc (0:ℝ) 1, ContDiffAt ℝ 2 φ t := by
      intro t ht
      exact fiber_path_C2at_on_segment f z ξ hTub_sub.isOpen hf_C2_on_U
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
  -- ── lyapunov_contraction_gen ───────────────────────────────────
  obtain ⟨Ω, _Ω_plus, R, hΩ_open, _, hR_pos, hm_in_Ω,
          hΩ_sub_Ωp, hΩp_sub_Up, hLC⟩ :=
    lyapunov_contraction_gen hd f L hL μ_minus hμ' θ hθ hθ_lt1 η rfl hη_pos
      ρ rfl S hS_argmin π hπ_in_S hπ_fix hgrad_zero
      P mstar hmstar ε hε_pos hε_bound hμη_lt1_pre
      U_plus hU_open hm_in
      hf_diffOn_Up hf_lip_Up
      hStrAim hHessLow hπ_kills_normal
      hP_self_adj hP_idem
      hSegment_hyp R_abs hR_abs_pos h_curv_absorb_hyp
  have hΩ_sub_Up : Ω ⊆ U_plus := hΩ_sub_Ωp.trans hΩp_sub_Up
  have hΩ_sub_U : Ω ⊆ U := hΩ_sub_Up.trans (subset_closure.trans hU_sub)
  -- Extract contraction for bootstrap
  have hcontract : ∀ (s₀ : NesterovState d) (n_step : ℕ),
      let s := nesterovSeqGen f η ρ s₀ n_step
      s.x ∈ Ω → s.lookahead η ∈ Ω →
      lyapunovOfState P μ_minus π f η s ≤ R ^ 2 →
      lyapunovOfState P μ_minus π f η (nesterovSeqGen f η ρ s₀ (n_step + 1)) ≤
        (1 - (1 - θ) * Real.sqrt (μ_minus * η)) *
        lyapunovOfState P μ_minus π f η s := by
    intro s₀ n_step _s hsx hslx hLn_bound
    exact (hLC s₀ n_step hsx hslx hLn_bound).1
  -- ── Motion bounds (derived from coercivity + Lipschitz) ────────
  have hmotion : ∃ (C_h : ℝ) (_ : 0 < C_h)
      (hstep_bound : ∀ (s₀ : NesterovState d) (n_step : ℕ),
        let s := nesterovSeqGen f η ρ s₀ n_step
        let Ln := lyapunovOfState P μ_minus π f η s
        s.x ∈ Ω → s.lookahead η ∈ Ω → Ln ≤ R ^ 2 →
        ‖stepDispOfState f η ρ s‖ ≤ C_h * Real.sqrt η * Real.sqrt Ln)
      (C_mov : ℝ) (_ : 0 < C_mov),
      ∀ (s₀ : NesterovState d) (n_step : ℕ),
        let s := nesterovSeqGen f η ρ s₀ n_step
        let s' := nesterovSeqGen f η ρ s₀ (n_step + 1)
        let Ln := lyapunovOfState P μ_minus π f η s
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
    -- State-based bounds helper
    have hbounds : ∀ (s : NesterovState d),
        s.x ∈ Ω →
        s.lookahead η ∈ Ω →
        ‖stepDispOfState f η ρ s‖ ≤ Ch * Real.sqrt η *
          Real.sqrt (lyapunovOfState P μ_minus π f η s) ∧
        ‖Real.sqrt η • (nesterovStep f η ρ s).v‖ ≤
          Cmov * Real.sqrt (lyapunovOfState P μ_minus π f η s) := by
      intro s hsx hslx
      set Ln := lyapunovOfState P μ_minus π f η s
      set s' := nesterovStep f η ρ s
      set gn := gradient f (s.lookahead η)
      set en := normalDispOfState π η s
      -- Coercivity (via Ω ⊆ U_plus)
      have hcoer_here := (hcoer_bound s (hΩ_sub_Up hsx) (hΩ_sub_Up hslx)).1
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
        have h2 : μ_minus * (K * Ln) = C_coer * Ln := by nlinarith
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
        change ‖gradient f (s.lookahead η)‖ ≤
          (↑L : ℝ) * ‖s.lookahead η - π (s.lookahead η)‖
        exact gradient_bound_from_lipschitz f L hf_lip _ _
          (hΩ_sub_U hslx)
          (hTub_sub.subset (hπ_in_S _))
          (hgrad_zero _ (hπ_in_S _))
      have hg_bound : ‖gn‖ ≤ Cg * Real.sqrt Ln := by
        calc ‖gn‖ ≤ (↑L : ℝ) * ‖en‖ := hg_raw
          _ ≤ (↑L : ℝ) * (Ce * Real.sqrt Ln) := by
              apply mul_le_mul_of_nonneg_left he_bound hL_nn
          _ = Cg * Real.sqrt Ln := by ring
      -- (4) s'.v = ρ • (s.v - √η • gn)
      have hv'_eq : s'.v = ρ • (s.v - Real.sqrt η • gn) := by
        simp only [s', nesterovStep, gn, NesterovState.lookahead]
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
      -- (6) stepDispOfState decomposition: h = √η • s'.v - η • gn
      have hhn_eq : stepDispOfState f η ρ s =
          Real.sqrt η • s'.v - η • gn := by
        simp only [stepDispOfState, s', nesterovStep, gn, NesterovState.lookahead]
        abel
      -- (7) Prove both bounds
      constructor
      · -- Step bound: ‖h‖ ≤ Ch * √η * √Ln
        have hstep_raw : ‖stepDispOfState f η ρ s‖ ≤
            |Real.sqrt η| * ‖s'.v‖ + |η| * ‖gn‖ := by
          rw [hhn_eq]
          exact step_bound s'.v gn (Real.sqrt η) η
        rw [abs_of_nonneg hsqrt_η_nn, abs_of_nonneg hη_nn] at hstep_raw
        have hsqrt_Ln_nn := Real.sqrt_nonneg Ln
        calc ‖stepDispOfState f η ρ s‖
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
    · intro s₀ n_step _s _Ln hsx hslx _hLn_le
      exact (hbounds (nesterovSeqGen f η ρ s₀ n_step) hsx hslx).1
    · intro s₀ n_step _s _s' _Ln hsx hslx _hLn_le
      -- nesterovSeqGen f η ρ s₀ (n_step + 1) = nesterovStep f η ρ (nesterovSeqGen f η ρ s₀ n_step)
      have heq : (nesterovSeqGen f η ρ s₀ (n_step + 1)).v =
          (nesterovStep f η ρ (nesterovSeqGen f η ρ s₀ n_step)).v := rfl
      rw [heq]
      exact (hbounds (nesterovSeqGen f η ρ s₀ n_step) hsx hslx).2
  obtain ⟨C_h, hC_h, hstep_bound, C_mov, hC_mov, hvel_bound⟩ := hmotion
  -- ── bootstrap_total_displacement_gen ───────────────────────────
  obtain ⟨δ_boot, r_ball, hδ_boot, hr_ball, hball_Ω, hboot_raw⟩ :=
    bootstrap_total_displacement_gen f μ_minus hμ' θ hθ hθ_lt1 η hη_pos
      hμη_lt1_pre ρ S hS_argmin π P Ω hΩ_open R hR_pos mstar hmstar hm_in_Ω
      hcontract C_h hC_h hstep_bound C_mov hC_mov hvel_bound
  -- ── Assemble the local result ──
  -- Derive ‖Pv‖ ≤ ‖v‖ from the Pythagorean identity
  have hP_norm : ∀ w : E d, ‖P w‖ ≤ ‖w‖ := by
    intro w
    have hPw_sq : ‖P w‖ ^ 2 ≤ ‖w‖ ^ 2 := by nlinarith [hP_ortho w, sq_nonneg ‖w - P w‖]
    calc ‖P w‖ = Real.sqrt (‖P w‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (‖w‖ ^ 2) := Real.sqrt_le_sqrt hPw_sq
      _ = ‖w‖ := Real.sqrt_sq (norm_nonneg _)
  refine ⟨Ω, δ_boot, r_ball, C_coer, hΩ_open, hm_in_Ω, hΩ_sub_U, hδ_boot, hr_ball, hC_coer,
    hball_Ω, hP_idem, hP_norm, hμη_lt1_pre, ?_, ?_⟩
  · -- Coercivity on Ω
    intro s hsx hslx
    exact (hcoer_bound s (hΩ_sub_Up hsx) (hΩ_sub_Up hslx)).1
  · -- Iterate conclusion (with fiber segment property)
    intro s₀ hs₀_x hs₀_la hL₀_small
    obtain ⟨h_Ω, h_ball, h_decay⟩ := hboot_raw s₀ hs₀_x hs₀_la hL₀_small
    exact ⟨h_Ω, h_ball, h_decay, fun j t ht0 ht1 =>
      h_seg _ (hΩ_sub_Up (h_Ω j).2) t ht0 ht1⟩


/-- Public theorem wrapper for `localConvergenceAtBasePointGenProof`. -/
theorem local_convergence_at_base_point_gen
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
    let P := fderiv ℝ π mstar
    ∃ (Ω : Set (E d)) (δ r_ball C_coer : ℝ),
      IsOpen Ω ∧ mstar ∈ Ω ∧ Ω ⊆ U ∧ 0 < δ ∧ 0 < r_ball ∧ 0 < C_coer ∧
      Metric.ball mstar r_ball ⊆ Ω ∧
      -- Projector properties (from π ∘ π = π and the tubular neighborhood)
      (∀ x : E d, P (P x) = P x) ∧
      (∀ v : E d, ‖P v‖ ≤ ‖v‖) ∧
      -- Parameter bound (derived from μ ≤ L)
      μ_minus * η < 1 ∧
      -- Coercivity on Ω (velocity + normal displacement bounded by Lyapunov)
      (∀ s : NesterovState d, s.x ∈ Ω → s.lookahead η ∈ Ω →
        ‖s.v‖ ^ 2 + μ_minus * ‖normalDispOfState π η s‖ ^ 2 ≤
          C_coer * lyapunovOfState P μ_minus π f η s) ∧
      -- Iterate behavior
      ∀ s₀ : NesterovState d,
        s₀.x ∈ Metric.ball mstar δ →
        s₀.lookahead η ∈ Metric.ball mstar δ →
        lyapunovOfState P μ_minus π f η s₀ ≤ δ ^ 2 →
        (∀ n : ℕ,
          (nesterovSeqGen f η ρ s₀ n).x ∈ Ω ∧
          (nesterovSeqGen f η ρ s₀ n).lookahead η ∈ Ω) ∧
        (∀ n : ℕ,
          (nesterovSeqGen f η ρ s₀ n).x ∈ Metric.ball mstar r_ball ∧
          (nesterovSeqGen f η ρ s₀ n).lookahead η ∈ Metric.ball mstar r_ball) ∧
        (∀ n : ℕ,
          lyapunovOfState P μ_minus π f η (nesterovSeqGen f η ρ s₀ (n + 1)) ≤
            (1 - (1 - θ) * Real.sqrt (μ_minus * η)) ^ (n + 1) *
            lyapunovOfState P μ_minus π f η s₀) ∧
        (∀ j : ℕ, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
          π ((nesterovSeqGen f η ρ s₀ j).lookahead η) +
            t • ((nesterovSeqGen f η ρ s₀ j).lookahead η -
                  π ((nesterovSeqGen f η ρ s₀ j).lookahead η)) ∈ U) := by
  exact localConvergenceAtBasePointGenProof (d := d) (hd := hd) (L := L) (hL := hL) (μ := μ)
    (hμ := hμ) (hμ_le_L := hμ_le_L) (μ_minus := μ_minus) (hμ_minus := hμ_minus)
    (hμ_minus_lt := hμ_minus_lt) (θ := θ) (hθ := hθ) (hθ_lt1 := hθ_lt1) (f := f) (S := S)
    (hrange := hrange) (U := U) (hTub_sub := hTub_sub) (hPL := hPL) (hf_C2 := hf_C2)
    (hf_lip := hf_lip) (π := π) (hπ_on_U := hπ_on_U) (hπ_fix := hπ_fix) (hπ_in_S := hπ_in_S)
    (hgrad_zero := hgrad_zero) (mstar := mstar) (hmstar := hmstar)

end PLAcceleratedNesterovLean
