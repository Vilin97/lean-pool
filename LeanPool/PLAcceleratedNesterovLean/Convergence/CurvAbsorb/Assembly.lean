/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.PLAcceleratedNesterovLean.Convergence.CurvAbsorb.Algebraic
import LeanPool.PLAcceleratedNesterovLean.Core.NesterovSeqGen
import LeanPool.PLAcceleratedNesterovLean.Convergence.StateContraction.AuxVarRecursion
import LeanPool.PLAcceleratedNesterovLean.Convergence.LyapunovContraction.AuxVar

/-!
# Curvature Absorption Assembly

Standalone proof that the curvature + projector-freezing perturbation is absorbable.
Extracted from the main theorem to keep its proof term small (avoids kernel slowdown).

The key idea: Dπ is continuous at m⋆, so for small enough R,
all perturbation terms are O(ε₁ · Ln) with ε₁ = sup ‖Dπ-P‖ → 0.
-/

open scoped NNReal
noncomputable section

namespace PLAcceleratedNesterovLean


variable {d : ℕ}
-- Notation for ℝ^d
local notation "E" => EuclideanSpace ℝ (Fin d)

-- Assembly involves many sub-lemma calls requiring extra elaboration
/-- Assembly of the curvature absorption bound.

Given coercivity bounds, Dπ continuity at m⋆, and the algebraic lemmas
(xi_bound_mvt, proj_normal_bound, nesterov_step_bound, auxVar_recursion),
choose R_abs > 0 so that within B(m⋆, R_abs) with L_n ≤ R_abs²,
the total perturbation δ_curv + proj_err ≤ θ·a · L_n.

This is the formal curvature-absorption step: continuity
of `Dπ` near the base minimizer makes both the curvature error and the
projector-freezing term smaller than the chosen `θ`-fraction of the affine
decrement. -/
private abbrev curvAbsorbAssemblyProof
    (f : E → ℝ) (L : ℝ≥0) (hL : 0 < (L : ℝ))
    (μ' : ℝ) (hμ' : 0 < μ')
    (θ : ℝ) (hθ_pos : 0 < θ)
    (η ρ : ℝ)
    (hη_pos : 0 < η)
    (hμη_lt1 : μ' * η < 1)
    (hρ_eq : ρ = (1 - Real.sqrt (μ' * η)) / (1 + Real.sqrt (μ' * η)))
    (S : Set E)
    (π : E → E)
    (P : E →L[ℝ] E)
    (hP_ortho : ∀ v : E, ‖v‖ ^ 2 = ‖P v‖ ^ 2 + ‖v - P v‖ ^ 2)
    (mstar : E) (hmstar : mstar ∈ S)
    (hP_eq : P = fderiv ℝ π mstar)
    (U_plus : Set E) (hU_open : IsOpen U_plus) (hm_in : mstar ∈ U_plus)
    (U : Set E) (hU_isopen : IsOpen U) (hU_sub : closure U_plus ⊆ U)
    (hf_lip : LipschitzOnWith L (gradient f) U)
    (hS_sub_U : S ⊆ U)
    (hmstar_U : mstar ∈ U)
    (hπ_on_U : ∀ x ∈ U, π x ∈ S ∧ dist x (π x) = Metric.infDist x S)
    (hDπ_cont : ContinuousAt (fun x => fderiv ℝ π x) mstar)
    (C_coer : ℝ) (hC_coer : 0 < C_coer)
    (hcoer_bound : ∀ (x₁ : E) (n : ℕ),
        (nesterovSeq f η ρ x₁ n).x ∈ U_plus →
        (nesterovSeq f η ρ x₁ n).lookahead η ∈ U_plus →
        ‖(nesterovSeq f η ρ x₁ n).v‖ ^ 2 +
          μ' * ‖normalDisp π f η ρ x₁ n‖ ^ 2 ≤
          C_coer * lyapunov P μ' π f η ρ x₁ n)
    (hπ_kills_normal : ∀ x ∈ U_plus, fderiv ℝ π (π x) (x - π x) = 0)
    (hgrad_zero : ∀ x ∈ S, gradient f x = 0)
    (hπ_diff_near : ∃ δ_diff > 0, ∀ z ∈ Metric.ball mstar δ_diff, DifferentiableAt ℝ π z) :
    ∃ R_abs : ℝ, 0 < R_abs ∧ ∀ (x₁ : E) (n : ℕ),
        (nesterovSeq f η ρ x₁ n).x ∈ Metric.ball mstar R_abs →
        (nesterovSeq f η ρ x₁ n).lookahead η ∈ Metric.ball mstar R_abs →
        lyapunov P μ' π f η ρ x₁ n ≤ R_abs ^ 2 →
        let sn := nesterovSeq f η ρ x₁ n
        let gn := gradient f (sn.lookahead η)
        let en := sn.lookahead η - π (sn.lookahead η)
        let ξn := curvatureError (↑P) π f η ρ x₁ n
        let un1 := auxVar P μ' π f η ρ x₁ (n + 1)
        let wn := un1 - Real.sqrt μ' • ξn
        let δ_curv := Real.sqrt μ' * @inner ℝ _ _ wn ξn +
                      (Real.sqrt μ') ^ 2 / 2 * ‖ξn‖ ^ 2
        let a := Real.sqrt (μ' * η)
        let Ln := lyapunov P μ' π f η ρ x₁ n
        let proj_err := a * abs (@inner ℝ _ _ gn (P en))
        δ_curv + proj_err ≤ θ * a * Ln := by
  -- Derived positivity
  have hη_nn : (0 : ℝ) ≤ η := le_of_lt hη_pos
  have hμ'_pos : (0 : ℝ) < μ' := hμ'
  set sm := Real.sqrt μ'
  set sa := Real.sqrt (μ' * η)
  have hsm_pos : (0 : ℝ) < sm := Real.sqrt_pos_of_pos hμ'_pos
  have hsm_nn : (0 : ℝ) ≤ sm := le_of_lt hsm_pos
  have hsa_pos : (0 : ℝ) < sa := Real.sqrt_pos_of_pos (mul_pos hμ'_pos hη_pos)
  have hsa_lt1 : sa < 1 := by
    calc sa < Real.sqrt 1 := Real.sqrt_lt_sqrt (le_of_lt (mul_pos hμ'_pos hη_pos)) hμη_lt1
      _ = 1 := Real.sqrt_one
  -- Energy constants from coercivity: ‖v‖² + μ'·‖e‖² ≤ C_coer·Ln
  let Ce := Real.sqrt (C_coer / μ')
  let Cg := (↑L : ℝ) * Ce
  let Cv := Real.sqrt C_coer
  let Ch := η * Cg + Real.sqrt η * |ρ| * (Cv + Real.sqrt η * Cg)
  let Cw := Cv + sm * Ce + Real.sqrt η * Cg
  have hCe_nn : (0 : ℝ) ≤ Ce := Real.sqrt_nonneg _
  have hCg_nn : (0 : ℝ) ≤ Cg := mul_nonneg (NNReal.coe_nonneg L) hCe_nn
  have hCv_nn : (0 : ℝ) ≤ Cv := Real.sqrt_nonneg _
  have hCh_nn : (0 : ℝ) ≤ Ch :=
    add_nonneg (mul_nonneg hη_nn hCg_nn)
      (mul_nonneg (mul_nonneg (Real.sqrt_nonneg η) (abs_nonneg ρ))
        (add_nonneg hCv_nn (mul_nonneg (Real.sqrt_nonneg η) hCg_nn)))
  have hCw_nn : (0 : ℝ) ≤ Cw :=
    add_nonneg (add_nonneg hCv_nn (mul_nonneg hsm_nn hCe_nn))
      (mul_nonneg (Real.sqrt_nonneg η) hCg_nn)
  -- K: total perturbation constant (with +1 slack for strict inequality)
  let K := sm * Cw * Ch + sm ^ 2 / 2 * Ch ^ 2 + sa * Cg * Ce + 1
  have hK_pos : (0 : ℝ) < K := by
    change (0 : ℝ) < sm * Cw * Ch + sm ^ 2 / 2 * Ch ^ 2 + sa * Cg * Ce + 1
    have := mul_nonneg (mul_nonneg hsm_nn hCw_nn) hCh_nn
    have := mul_nonneg (div_nonneg (sq_nonneg sm) (by norm_num : (0:ℝ) ≤ 2)) (sq_nonneg Ch)
    have := mul_nonneg (mul_nonneg (le_of_lt hsa_pos) hCg_nn) hCe_nn
    linarith
  -- ε₁ = min(1, θ·sa/K)
  let ε₁ := min 1 (θ * sa / K)
  have hε₁_pos : (0 : ℝ) < ε₁ := lt_min one_pos (div_pos (mul_pos hθ_pos hsa_pos) hK_pos)
  have hε₁_le1 : ε₁ ≤ 1 := min_le_left _ _
  have hε₁K_le : ε₁ * K ≤ θ * sa := by
    calc ε₁ * K ≤ θ * sa / K * K := by gcongr; exact min_le_right _ _
      _ = θ * sa := by
          rw [div_mul_cancel₀ _ (ne_of_gt hK_pos)]
  -- Get δ_Dπ from Dπ continuity at mstar
  -- Since P = fderiv ℝ π mstar, this gives ‖fderiv ℝ π z - P‖ < ε₁ near mstar
  rw [Metric.continuousAt_iff] at hDπ_cont
  obtain ⟨δ_Dπ, hδ_Dπ_pos, hδ_Dπ⟩ := hDπ_cont ε₁ hε₁_pos
  -- Get δ_Up with B(mstar, δ_Up) ⊆ U_plus
  obtain ⟨δ_Up, hδ_Up_pos, hδ_Up_sub⟩ := Metric.isOpen_iff.mp hU_open mstar hm_in
  -- Get δ_U with B(mstar, δ_U) ⊆ U
  obtain ⟨δ_U, hδ_U_pos, hδ_U_sub⟩ := Metric.isOpen_iff.mp hU_isopen mstar hmstar_U
  -- Get δ_diff with differentiability on B(mstar, δ_diff)
  obtain ⟨δ_diff, hδ_diff_pos, hπ_diff_ball⟩ := hπ_diff_near
  -- Expansion factor: dist(πx, m*) ≤ 2·dist(x, m*), dist(x'n1, m*) ≤ (1+Ch)·R
  let M := 2 + Ch + 1
  have hM_ge3 : (3 : ℝ) ≤ M := by linarith [hCh_nn]
  -- R₀ ensures all relevant points are in B(mstar, δ_Dπ) ∩ U ∩ diff ball
  let R₀ := min (min (min δ_Up δ_U) δ_Dπ) δ_diff / (M + 1)
  have hMp1_pos : (0 : ℝ) < M + 1 := by linarith [hCh_nn]
  have hR₀_pos : (0 : ℝ) < R₀ :=
    div_pos (lt_min (lt_min (lt_min hδ_Up_pos hδ_U_pos) hδ_Dπ_pos) hδ_diff_pos) hMp1_pos
  refine ⟨R₀, hR₀_pos, ?_⟩
  intro x₁ n hsx hslx hLn_le
  -- Abbreviations
  set sn := nesterovSeq f η ρ x₁ n
  set x'n := sn.lookahead η
  set gn := gradient f x'n
  set en := x'n - π x'n
  set hn := nesterovH f η ρ x₁ n
  set ξn := curvatureError (↑P) π f η ρ x₁ n
  set un1 := auxVar P μ' π f η ρ x₁ (n + 1)
  set wn := un1 - sm • ξn
  set Ln := lyapunov P μ' π f η ρ x₁ n
  -- R₀ ≤ various δ's
  have hMp1R₀ : (M + 1) * R₀ = min (min (min δ_Up δ_U) δ_Dπ) δ_diff :=
    mul_div_cancel₀ _ (ne_of_gt hMp1_pos)
  have hR₀_le_δUp : R₀ ≤ δ_Up := by
    calc R₀ ≤ (M + 1) * R₀ :=
          le_mul_of_one_le_left (le_of_lt hR₀_pos) (by linarith [hCh_nn])
      _ = min (min (min δ_Up δ_U) δ_Dπ) δ_diff := hMp1R₀
      _ ≤ min (min δ_Up δ_U) δ_Dπ := min_le_left _ _
      _ ≤ min δ_Up δ_U := min_le_left _ _
      _ ≤ δ_Up := min_le_left _ _
  have hMR₀_lt_min : M * R₀ < min (min (min δ_Up δ_U) δ_Dπ) δ_diff := by
    linarith [hR₀_pos]
  have hMR₀_lt_δDπ : M * R₀ < δ_Dπ :=
    lt_of_lt_of_le hMR₀_lt_min
      ((min_le_left _ _).trans (min_le_right _ _))
  have hMR₀_lt_δU : M * R₀ < δ_U :=
    lt_of_lt_of_le hMR₀_lt_min
      ((min_le_left _ _).trans
        ((min_le_left _ _).trans (min_le_right _ _)))
  have hMR₀_lt_δdiff : M * R₀ < δ_diff :=
    lt_of_lt_of_le hMR₀_lt_min (min_le_right _ _)
  -- Location in U_plus and U
  have hx'n_Up : x'n ∈ U_plus :=
    hδ_Up_sub (Metric.ball_subset_ball hR₀_le_δUp hslx)
  have hx'n_U : x'n ∈ U := hU_sub (subset_closure hx'n_Up)
  have hsx_Up : sn.x ∈ U_plus :=
    hδ_Up_sub (Metric.ball_subset_ball hR₀_le_δUp hsx)
  -- Dπ bound: any z with dist(z, m*) < M·R₀ has ‖Dπ(z) - P‖ ≤ ε₁ and z ∈ U
  have hDπ_in_MR₀ : ∀ z, dist z mstar < M * R₀ →
      ‖fderiv ℝ π z - P‖ ≤ ε₁ ∧ z ∈ U := by
    intro z hz
    constructor
    · have h := hδ_Dπ (lt_trans hz hMR₀_lt_δDπ)
      rw [dist_eq_norm, ← hP_eq] at h; exact le_of_lt h
    · exact hδ_U_sub (Metric.mem_ball.mpr (lt_trans hz hMR₀_lt_δU))
  -- Coercivity at step n
  have hcoer := hcoer_bound x₁ n hsx_Up hx'n_Up
  have hnd : normalDisp π f η ρ x₁ n = en := rfl
  rw [hnd] at hcoer
  -- ‖v‖² ≤ C_coer·Ln, ‖e‖² ≤ C_coer/μ'·Ln
  have hv_sq : ‖sn.v‖ ^ 2 ≤ C_coer * Ln := by
    have := mul_nonneg (le_of_lt hμ'_pos) (sq_nonneg ‖en‖); linarith
  have he_sq : ‖en‖ ^ 2 ≤ C_coer / μ' * Ln := by
    have h1 : μ' * ‖en‖ ^ 2 ≤ C_coer * Ln := by have := sq_nonneg ‖sn.v‖; linarith
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hμ'_pos).mpr (by linarith)
  -- Ln ≥ 0
  have hLn_nn : (0 : ℝ) ≤ Ln := by
    have h1 := sq_nonneg ‖sn.v‖
    have h2 := mul_nonneg (le_of_lt hμ'_pos) (sq_nonneg ‖en‖)
    exact nonneg_of_mul_nonneg_left (by linarith) hC_coer
  -- √Ln ≤ R₀
  have hLn_sqrt : Real.sqrt Ln ≤ R₀ := by
    calc Real.sqrt Ln ≤ Real.sqrt (R₀ ^ 2) := Real.sqrt_le_sqrt hLn_le
      _ = R₀ := Real.sqrt_sq (le_of_lt hR₀_pos)
  -- Key helper: √Ln * √Ln = Ln
  have hsqrt_sq : Real.sqrt Ln * Real.sqrt Ln = Ln := Real.mul_self_sqrt hLn_nn
  -- Helper: a² ≤ C·L → a ≤ √C · √L
  have sqrt_bound : ∀ {a C L : ℝ}, 0 ≤ a → 0 ≤ C → 0 ≤ L →
      a ^ 2 ≤ C * L → a ≤ Real.sqrt C * Real.sqrt L := by
    intro a C L ha hC hL hab
    calc a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha).symm
      _ ≤ Real.sqrt (C * L) := Real.sqrt_le_sqrt hab
      _ = Real.sqrt C * Real.sqrt L := Real.sqrt_mul hC L
  -- ‖e‖ ≤ Ce·√Ln, ‖v‖ ≤ Cv·√Ln
  have he_bound : ‖en‖ ≤ Ce * Real.sqrt Ln :=
    sqrt_bound (norm_nonneg _) (div_nonneg (le_of_lt hC_coer) (le_of_lt hμ'_pos)) hLn_nn he_sq
  have hv_bound : ‖sn.v‖ ≤ Cv * Real.sqrt Ln :=
    sqrt_bound (norm_nonneg _) (le_of_lt hC_coer) hLn_nn hv_sq
  -- ‖g‖ ≤ L·‖e‖ (gradient Lipschitz + ∇f|_S = 0)
  have hgn_bound : ‖gn‖ ≤ (↑L : ℝ) * ‖en‖ := by
    have := hf_lip.dist_le_mul x'n (hU_sub (subset_closure hx'n_Up))
      (π x'n) (hS_sub_U (hπ_on_U x'n hx'n_U).1)
    rwa [hgrad_zero (π x'n) (hπ_on_U x'n hx'n_U).1, dist_zero_right, dist_eq_norm] at this
  have hg_bound : ‖gn‖ ≤ Cg * Real.sqrt Ln := by
    calc ‖gn‖ ≤ (↑L : ℝ) * ‖en‖ := hgn_bound
      _ ≤ (↑L : ℝ) * (Ce * Real.sqrt Ln) := by gcongr
      _ = Cg * Real.sqrt Ln := by ring
  -- ‖h‖ ≤ Ch·√Ln (nesterov_step_bound)
  have hhn_bound : ‖hn‖ ≤ Ch * Real.sqrt Ln := by
    change ‖nesterovH f η ρ x₁ n‖ ≤ _
    unfold nesterovH
    rw [show nesterovSeq f η ρ x₁ (n + 1) =
      nesterovStep f η ρ (nesterovSeq f η ρ x₁ n) from rfl]
    calc ‖(nesterovStep f η ρ (nesterovSeq f η ρ x₁ n)).lookahead η -
            (nesterovSeq f η ρ x₁ n).lookahead η‖
        ≤ η * ‖gradient f ((nesterovSeq f η ρ x₁ n).lookahead η)‖ +
          Real.sqrt η * |ρ| * (‖(nesterovSeq f η ρ x₁ n).v‖ +
          Real.sqrt η * ‖gradient f ((nesterovSeq f η ρ x₁ n).lookahead η)‖) :=
          nesterov_step_bound f η ρ (nesterovSeq f η ρ x₁ n) hη_nn
      _ ≤ η * (Cg * Real.sqrt Ln) + Real.sqrt η * |ρ| *
          (Cv * Real.sqrt Ln + Real.sqrt η * (Cg * Real.sqrt Ln)) := by
          gcongr
      _ = Ch * Real.sqrt Ln := by ring
  -- ── π(x'n) ∈ B(mstar, 2R₀) ──
  have hπx'n_dist : dist (π x'n) mstar < 2 * R₀ := by
    have hd1 := Metric.mem_ball.mp hslx
    have := (hπ_on_U x'n hx'n_U).2
    have hπe : dist x'n (π x'n) ≤ dist x'n mstar :=
      this ▸ Metric.infDist_le_dist_of_mem hmstar
    linarith [dist_triangle (π x'n) x'n mstar, dist_comm (π x'n) x'n]
  -- ── x'_{n+1} ∈ B(mstar, (1+Ch)·R₀) ──
  have hx'n1_eq : (nesterovSeq f η ρ x₁ (n + 1)).lookahead η = x'n + hn := by
    change (nesterovSeq f η ρ x₁ (n + 1)).lookahead η =
      (nesterovSeq f η ρ x₁ n).lookahead η + nesterovH f η ρ x₁ n
    unfold nesterovH; abel
  have hx'n1_dist : dist (x'n + hn) mstar < (1 + Ch) * R₀ := by
    have hd1 := Metric.mem_ball.mp hslx
    have hhn_le : ‖hn‖ ≤ Ch * R₀ :=
      le_trans hhn_bound (mul_le_mul_of_nonneg_left hLn_sqrt hCh_nn)
    linarith [dist_triangle (x'n + hn) x'n mstar,
              show dist (x'n + hn) x'n = ‖hn‖ from by rw [dist_eq_norm, add_sub_cancel_left]]
  -- Both points in Dπ-controlled region (dist < M·R₀)
  have hMR₀_ge_2R₀ : 2 * R₀ ≤ M * R₀ :=
    mul_le_mul_of_nonneg_right (by linarith [hM_ge3]) (le_of_lt hR₀_pos)
  have hMR₀_ge_1ChR₀ : (1 + Ch) * R₀ ≤ M * R₀ :=
    mul_le_mul_of_nonneg_right (by linarith [hCh_nn]) (le_of_lt hR₀_pos)
  have hπx'n_ctrl : dist (π x'n) mstar < M * R₀ := by
    linarith [hπx'n_dist]
  have hx'n_ctrl : dist x'n mstar < M * R₀ := by
    have := Metric.mem_ball.mp hslx; linarith
  have hx'n1_ctrl : dist (x'n + hn) mstar < M * R₀ := by
    linarith [hx'n1_dist]
  -- ‖Dπ(π(x'n)) - P‖ ≤ ε₁
  have hDπ_πx'n : ‖fderiv ℝ π (π x'n) - P‖ ≤ ε₁ :=
    (hDπ_in_MR₀ (π x'n) hπx'n_ctrl).1
  -- ── ‖P en‖ ≤ ε₁·‖en‖ ──
  have hPen : ‖P en‖ ≤ ε₁ * ‖en‖ :=
    proj_normal_bound P π x'n (hπ_kills_normal x'n hx'n_Up) ε₁ hDπ_πx'n
  -- ── ‖ξn‖ ≤ ε₁·‖hn‖ ──
  have hξn_bound : ‖ξn‖ ≤ ε₁ * ‖hn‖ := by
    -- First get the MVT bound
    have hmvt := xi_bound_mvt P π x'n (x'n + hn) mstar (M * R₀)
      (Metric.mem_ball.mpr hx'n_ctrl) (Metric.mem_ball.mpr hx'n1_ctrl)
      (fun z hz => hπ_diff_ball z (Metric.ball_subset_ball (le_of_lt hMR₀_lt_δdiff) hz)) ε₁
      (fun z hz => (hDπ_in_MR₀ z (Metric.mem_ball.mp hz)).1)
    -- hmvt : ‖P ((x'n + hn) - x'n) - (π (x'n + hn) - π x'n)‖ ≤ ε₁ * ‖(x'n + hn) - x'n‖
    simp only [add_sub_cancel_left] at hmvt
    -- hmvt : ‖P hn - (π (x'n + hn) - π x'n)‖ ≤ ε₁ * ‖hn‖
    -- Now show ξn equals P hn - (π(x'n+hn) - π x'n)
    suffices hsuff : (ξn : E) = P hn - (π (x'n + hn) - π x'n) by rw [hsuff]; exact hmvt
    change curvatureError (↑P) π f η ρ x₁ n = _
    unfold curvatureError normalDisp
    rw [hx'n1_eq]
    simp only []
    -- After clearing lets: LHS is in terms of x'n, hn, π, (↑P)
    -- RHS is P hn - (π(x'n+hn) - π x'n)
    -- These are equal by algebra (↑P and P are definitionally equal)
    abel
  -- ── ‖wn‖ ≤ Cw·√Ln (via auxVar_recursion) ──
  have hwn_eq : (wn : E) = (1 - sa) • (sn.v - P sn.v) +
      sm • en - Real.sqrt η • (gn - P gn) := by
    change un1 - sm • ξn = _
    have h_av := auxVar_recursion P μ' η ρ π f x₁ n hρ_eq hsa_pos hη_pos hμ'_pos
    have : (un1 : E) = ((1 - sa) • (sn.v - P sn.v) + sm • en -
        Real.sqrt η • (gn - P gn)) + sm • ξn := by
      change auxVar P μ' π f η ρ x₁ (n + 1) = _; exact h_av
    rw [this]; abel
  have hwn_bound : ‖wn‖ ≤ Cw * Real.sqrt Ln := by
    rw [hwn_eq]
    have h1 : ‖(1 - sa) • (sn.v - P sn.v)‖ ≤ ‖sn.v - P sn.v‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      calc |1 - sa| * ‖sn.v - P sn.v‖ ≤ 1 * ‖sn.v - P sn.v‖ := by
            gcongr; rw [abs_le]; exact ⟨by linarith [hsa_pos], by linarith [hsa_lt1]⟩
        _ = ‖sn.v - P sn.v‖ := one_mul _
    have hPv_sub : ‖sn.v - P sn.v‖ ≤ ‖sn.v‖ := by
      rw [← Real.sqrt_sq (norm_nonneg sn.v), ← Real.sqrt_sq (norm_nonneg (sn.v - P sn.v))]
      exact Real.sqrt_le_sqrt (by have := hP_ortho sn.v; have := sq_nonneg ‖P sn.v‖; linarith)
    have hPg_sub : ‖gn - P gn‖ ≤ ‖gn‖ := by
      rw [← Real.sqrt_sq (norm_nonneg gn), ← Real.sqrt_sq (norm_nonneg (gn - P gn))]
      exact Real.sqrt_le_sqrt (by have := hP_ortho gn; have := sq_nonneg ‖P gn‖; linarith)
    calc ‖(1 - sa) • (sn.v - P sn.v) + sm • en - Real.sqrt η • (gn - P gn)‖
        ≤ ‖(1 - sa) • (sn.v - P sn.v)‖ + ‖sm • en‖ + ‖Real.sqrt η • (gn - P gn)‖ := by
          calc ‖(1 - sa) • (sn.v - P sn.v) + sm • en - Real.sqrt η • (gn - P gn)‖
              ≤ ‖(1 - sa) • (sn.v - P sn.v) + sm • en‖ +
                ‖Real.sqrt η • (gn - P gn)‖ := norm_sub_le _ _
            _ ≤ (‖(1 - sa) • (sn.v - P sn.v)‖ + ‖sm • en‖) +
                ‖Real.sqrt η • (gn - P gn)‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ‖sn.v‖ + sm * ‖en‖ + Real.sqrt η * ‖gn‖ := by
          have hsm_e : ‖sm • en‖ = sm * ‖en‖ := by
            rw [norm_smul, Real.norm_of_nonneg hsm_nn]
          have hη_g : ‖Real.sqrt η • (gn - P gn)‖ = Real.sqrt η * ‖gn - P gn‖ := by
            rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg η)]
          have hh1 : ‖(1 - sa) • (sn.v - P sn.v)‖ ≤ ‖sn.v‖ := h1.trans hPv_sub
          have hh3 : Real.sqrt η * ‖gn - P gn‖ ≤ Real.sqrt η * ‖gn‖ :=
            mul_le_mul_of_nonneg_left hPg_sub (Real.sqrt_nonneg η)
          linarith [hsm_e, hη_g, hh1, hh3]
      _ ≤ Cv * Real.sqrt Ln + sm * (Ce * Real.sqrt Ln) +
          Real.sqrt η * (Cg * Real.sqrt Ln) := by gcongr
      _ = Cw * Real.sqrt Ln := by ring
  -- ── Bound δ_curv + proj_err ──
  have hCS_wξ := real_inner_le_norm wn ξn
  -- ‖ξn‖² ≤ ε₁ · Ch² · Ln
  have hξn_sq : ‖ξn‖ ^ 2 ≤ ε₁ * Ch ^ 2 * Ln := by
    have h1 : ‖ξn‖ ≤ ε₁ * (Ch * Real.sqrt Ln) := by
      calc ‖ξn‖ ≤ ε₁ * ‖hn‖ := hξn_bound
        _ ≤ ε₁ * (Ch * Real.sqrt Ln) := by gcongr
    have h2 : ‖ξn‖ ^ 2 ≤ (ε₁ * (Ch * Real.sqrt Ln)) ^ 2 :=
      sq_le_sq' (by linarith [norm_nonneg ξn]) h1
    have h3 : (ε₁ * (Ch * Real.sqrt Ln)) ^ 2 = ε₁ ^ 2 * Ch ^ 2 * Ln := by
      calc (ε₁ * (Ch * Real.sqrt Ln)) ^ 2
          = ε₁ ^ 2 * Ch ^ 2 * (Real.sqrt Ln * Real.sqrt Ln) := by ring
        _ = ε₁ ^ 2 * Ch ^ 2 * Ln := by rw [hsqrt_sq]
    have h4 : ε₁ ^ 2 ≤ ε₁ := by
      calc ε₁ ^ 2 = ε₁ * ε₁ := sq ε₁
        _ ≤ ε₁ * 1 := mul_le_mul_of_nonneg_left hε₁_le1 (le_of_lt hε₁_pos)
        _ = ε₁ := mul_one ε₁
    calc ‖ξn‖ ^ 2 ≤ ε₁ ^ 2 * Ch ^ 2 * Ln := by linarith
      _ ≤ ε₁ * Ch ^ 2 * Ln := by
          have h5 := mul_le_mul_of_nonneg_right h4 (mul_nonneg (sq_nonneg Ch) hLn_nn)
          linarith
  -- δ_curv bound
  have hδ_curv : sm * @inner ℝ _ _ wn ξn + sm ^ 2 / 2 * ‖ξn‖ ^ 2 ≤
      ε₁ * (sm * Cw * Ch + sm ^ 2 / 2 * Ch ^ 2) * Ln := by
    have ht1 : sm * @inner ℝ _ _ wn ξn ≤ ε₁ * (sm * Cw * Ch) * Ln := by
      have h1 : sm * @inner ℝ _ _ wn ξn ≤ sm * (‖wn‖ * ‖ξn‖) :=
        mul_le_mul_of_nonneg_left hCS_wξ hsm_nn
      have h2 : ‖wn‖ * ‖ξn‖ ≤ (Cw * Real.sqrt Ln) * (ε₁ * (Ch * Real.sqrt Ln)) := by
        gcongr
        calc ‖ξn‖ ≤ ε₁ * ‖hn‖ := hξn_bound
          _ ≤ ε₁ * (Ch * Real.sqrt Ln) := by gcongr
      have h3 : (Cw * Real.sqrt Ln) * (ε₁ * (Ch * Real.sqrt Ln)) =
          ε₁ * Cw * Ch * Ln := by
        calc (Cw * Real.sqrt Ln) * (ε₁ * (Ch * Real.sqrt Ln))
            = ε₁ * Cw * Ch * (Real.sqrt Ln * Real.sqrt Ln) := by ring
          _ = ε₁ * Cw * Ch * Ln := by rw [hsqrt_sq]
      have h4 : sm * (‖wn‖ * ‖ξn‖) ≤ sm * (ε₁ * Cw * Ch * Ln) :=
        mul_le_mul_of_nonneg_left (le_trans h2 (le_of_eq h3)) hsm_nn
      calc sm * @inner ℝ _ _ wn ξn
          ≤ sm * (‖wn‖ * ‖ξn‖) := h1
        _ ≤ sm * (ε₁ * Cw * Ch * Ln) := h4
        _ = ε₁ * (sm * Cw * Ch) * Ln := by ring
    have ht2 : sm ^ 2 / 2 * ‖ξn‖ ^ 2 ≤ ε₁ * (sm ^ 2 / 2 * Ch ^ 2) * Ln := by
      have hsm2 : (0:ℝ) ≤ sm ^ 2 / 2 := div_nonneg (sq_nonneg sm) (by norm_num : (0:ℝ) ≤ 2)
      calc sm ^ 2 / 2 * ‖ξn‖ ^ 2
          ≤ sm ^ 2 / 2 * (ε₁ * Ch ^ 2 * Ln) := mul_le_mul_of_nonneg_left hξn_sq hsm2
        _ = ε₁ * (sm ^ 2 / 2 * Ch ^ 2) * Ln := by ring
    calc sm * @inner ℝ _ _ wn ξn + sm ^ 2 / 2 * ‖ξn‖ ^ 2
        ≤ ε₁ * (sm * Cw * Ch) * Ln + ε₁ * (sm ^ 2 / 2 * Ch ^ 2) * Ln :=
          add_le_add ht1 ht2
      _ = ε₁ * (sm * Cw * Ch + sm ^ 2 / 2 * Ch ^ 2) * Ln := by ring
  -- proj_err bound
  have hproj : sa * |@inner ℝ _ _ gn (P en)| ≤ ε₁ * (sa * Cg * Ce) * Ln := by
    have hCS_gPe := abs_real_inner_le_norm gn (P en)
    have h1 : ‖gn‖ * ‖P en‖ ≤ ‖gn‖ * (ε₁ * ‖en‖) :=
      mul_le_mul_of_nonneg_left hPen (norm_nonneg _)
    have h2 : ‖gn‖ * (ε₁ * ‖en‖) ≤ (Cg * Real.sqrt Ln) * (ε₁ * (Ce * Real.sqrt Ln)) := by
      gcongr
    have h3 : (Cg * Real.sqrt Ln) * (ε₁ * (Ce * Real.sqrt Ln)) = ε₁ * Cg * Ce * Ln := by
      calc (Cg * Real.sqrt Ln) * (ε₁ * (Ce * Real.sqrt Ln))
          = ε₁ * Cg * Ce * (Real.sqrt Ln * Real.sqrt Ln) := by ring
        _ = ε₁ * Cg * Ce * Ln := by rw [hsqrt_sq]
    calc sa * |@inner ℝ _ _ gn (P en)|
        ≤ sa * (ε₁ * Cg * Ce * Ln) :=
          mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hsa_pos)
      _ = ε₁ * (sa * Cg * Ce) * Ln := by ring
  -- Assembly: total ≤ ε₁·K·Ln ≤ θ·sa·Ln
  calc sm * @inner ℝ _ _ wn ξn + sm ^ 2 / 2 * ‖ξn‖ ^ 2 +
        sa * |@inner ℝ _ _ gn (P en)|
      ≤ ε₁ * (sm * Cw * Ch + sm ^ 2 / 2 * Ch ^ 2) * Ln +
        ε₁ * (sa * Cg * Ce) * Ln := add_le_add hδ_curv hproj
    _ = ε₁ * (sm * Cw * Ch + sm ^ 2 / 2 * Ch ^ 2 + sa * Cg * Ce) * Ln := by ring
    _ ≤ ε₁ * K * Ln :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (by change sm * Cw * Ch + sm ^ 2 / 2 * Ch ^ 2 + sa * Cg * Ce ≤
                  sm * Cw * Ch + sm ^ 2 / 2 * Ch ^ 2 + sa * Cg * Ce + 1; linarith)
            (le_of_lt hε₁_pos))
          hLn_nn
    _ ≤ θ * sa * Ln :=
        mul_le_mul_of_nonneg_right hε₁K_le hLn_nn

/-- Assembly of the curvature absorption bound.

Given coercivity bounds, Dπ continuity at m⋆, and the algebraic lemmas
(xi_bound_mvt, proj_normal_bound, nesterov_step_bound, auxVarOfState_step),
choose R_abs > 0 so that within B(m⋆, R_abs) with L_n ≤ R_abs²,
the total perturbation δ_curv + proj_err ≤ θ·a · L_n.

This is the state-based curvature-absorption step.  The
budget-split parameter θ ∈ (0,1) controls what fraction of the affine decrement
is reserved for the curvature and projector-freezing errors.

Generalized to arbitrary initial state s₀ (not just zero velocity). -/
private abbrev curvAbsorbAssemblyGenProof
    (f : E → ℝ) (L : ℝ≥0) (hL : 0 < (L : ℝ))
    (μ' : ℝ) (hμ' : 0 < μ')
    (θ : ℝ) (hθ_pos : 0 < θ)
    (η ρ : ℝ)
    (hη_pos : 0 < η)
    (hμη_lt1 : μ' * η < 1)
    (hρ_eq : ρ = (1 - Real.sqrt (μ' * η)) / (1 + Real.sqrt (μ' * η)))
    (S : Set E)
    (π : E → E)
    (P : E →L[ℝ] E)
    (hP_ortho : ∀ v : E, ‖v‖ ^ 2 = ‖P v‖ ^ 2 + ‖v - P v‖ ^ 2)
    (mstar : E) (hmstar : mstar ∈ S)
    (hP_eq : P = fderiv ℝ π mstar)
    (U_plus : Set E) (hU_open : IsOpen U_plus) (hm_in : mstar ∈ U_plus)
    (U : Set E) (hU_isopen : IsOpen U) (hU_sub : closure U_plus ⊆ U)
    (hf_lip : LipschitzOnWith L (gradient f) U)
    (hS_sub_U : S ⊆ U)
    (hmstar_U : mstar ∈ U)
    (hπ_on_U : ∀ x ∈ U, π x ∈ S ∧ dist x (π x) = Metric.infDist x S)
    (hDπ_cont : ContinuousAt (fun x => fderiv ℝ π x) mstar)
    (C_coer : ℝ) (hC_coer : 0 < C_coer)
    (hcoer_bound : ∀ (s : NesterovState d),
        s.x ∈ U_plus →
        s.lookahead η ∈ U_plus →
        ‖s.v‖ ^ 2 +
          μ' * ‖normalDispOfState π η s‖ ^ 2 ≤
          C_coer * lyapunovOfState P μ' π f η s)
    (hπ_kills_normal : ∀ x ∈ U_plus, fderiv ℝ π (π x) (x - π x) = 0)
    (hgrad_zero : ∀ x ∈ S, gradient f x = 0)
    (hπ_diff_near : ∃ δ_diff > 0, ∀ z ∈ Metric.ball mstar δ_diff, DifferentiableAt ℝ π z) :
    ∃ R_abs : ℝ, 0 < R_abs ∧ ∀ (s₀ : NesterovState d) (n : ℕ),
        (nesterovSeqGen f η ρ s₀ n).x ∈ Metric.ball mstar R_abs →
        (nesterovSeqGen f η ρ s₀ n).lookahead η ∈ Metric.ball mstar R_abs →
        lyapunovOfState P μ' π f η (nesterovSeqGen f η ρ s₀ n) ≤ R_abs ^ 2 →
        let sn := nesterovSeqGen f η ρ s₀ n
        let gn := gradient f (sn.lookahead η)
        let en := sn.lookahead η - π (sn.lookahead η)
        let ξn := curvatureErrorOfState (↑P) π f η ρ sn
        let un1 := auxVarOfState P μ' π η (nesterovStep f η ρ sn)
        let wn := un1 - Real.sqrt μ' • ξn
        let δ_curv := Real.sqrt μ' * @inner ℝ _ _ wn ξn +
                      (Real.sqrt μ') ^ 2 / 2 * ‖ξn‖ ^ 2
        let a := Real.sqrt (μ' * η)
        let Ln := lyapunovOfState P μ' π f η sn
        let proj_err := a * abs (@inner ℝ _ _ gn (P en))
        δ_curv + proj_err ≤ θ * a * Ln := by
  -- Derived positivity
  have hη_nn : (0 : ℝ) ≤ η := le_of_lt hη_pos
  have hμ'_pos : (0 : ℝ) < μ' := hμ'
  set sm := Real.sqrt μ'
  set sa := Real.sqrt (μ' * η)
  have hsm_pos : (0 : ℝ) < sm := Real.sqrt_pos_of_pos hμ'_pos
  have hsm_nn : (0 : ℝ) ≤ sm := le_of_lt hsm_pos
  have hsa_pos : (0 : ℝ) < sa := Real.sqrt_pos_of_pos (mul_pos hμ'_pos hη_pos)
  have hsa_lt1 : sa < 1 := by
    calc sa < Real.sqrt 1 := Real.sqrt_lt_sqrt (le_of_lt (mul_pos hμ'_pos hη_pos)) hμη_lt1
      _ = 1 := Real.sqrt_one
  -- Energy constants from coercivity: ‖v‖² + μ'·‖e‖² ≤ C_coer·Ln
  let Ce := Real.sqrt (C_coer / μ')
  let Cg := (↑L : ℝ) * Ce
  let Cv := Real.sqrt C_coer
  let Ch := η * Cg + Real.sqrt η * |ρ| * (Cv + Real.sqrt η * Cg)
  let Cw := Cv + sm * Ce + Real.sqrt η * Cg
  have hCe_nn : (0 : ℝ) ≤ Ce := Real.sqrt_nonneg _
  have hCg_nn : (0 : ℝ) ≤ Cg := mul_nonneg (NNReal.coe_nonneg L) hCe_nn
  have hCv_nn : (0 : ℝ) ≤ Cv := Real.sqrt_nonneg _
  have hCh_nn : (0 : ℝ) ≤ Ch :=
    add_nonneg (mul_nonneg hη_nn hCg_nn)
      (mul_nonneg (mul_nonneg (Real.sqrt_nonneg η) (abs_nonneg ρ))
        (add_nonneg hCv_nn (mul_nonneg (Real.sqrt_nonneg η) hCg_nn)))
  have hCw_nn : (0 : ℝ) ≤ Cw :=
    add_nonneg (add_nonneg hCv_nn (mul_nonneg hsm_nn hCe_nn))
      (mul_nonneg (Real.sqrt_nonneg η) hCg_nn)
  -- K: total perturbation constant (with +1 slack for strict inequality)
  let K := sm * Cw * Ch + sm ^ 2 / 2 * Ch ^ 2 + sa * Cg * Ce + 1
  have hK_pos : (0 : ℝ) < K := by
    change (0 : ℝ) < sm * Cw * Ch + sm ^ 2 / 2 * Ch ^ 2 + sa * Cg * Ce + 1
    have := mul_nonneg (mul_nonneg hsm_nn hCw_nn) hCh_nn
    have := mul_nonneg (div_nonneg (sq_nonneg sm) (by norm_num : (0:ℝ) ≤ 2)) (sq_nonneg Ch)
    have := mul_nonneg (mul_nonneg (le_of_lt hsa_pos) hCg_nn) hCe_nn
    linarith
  -- ε₁ = min(1, θ·sa/K)
  let ε₁ := min 1 (θ * sa / K)
  have hε₁_pos : (0 : ℝ) < ε₁ := lt_min one_pos (div_pos (mul_pos hθ_pos hsa_pos) hK_pos)
  have hε₁_le1 : ε₁ ≤ 1 := min_le_left _ _
  have hε₁K_le : ε₁ * K ≤ θ * sa := by
    calc ε₁ * K ≤ θ * sa / K * K := by gcongr; exact min_le_right _ _
      _ = θ * sa := by
          rw [div_mul_cancel₀ _ (ne_of_gt hK_pos)]
  -- Get δ_Dπ from Dπ continuity at mstar
  -- Since P = fderiv ℝ π mstar, this gives ‖fderiv ℝ π z - P‖ < ε₁ near mstar
  rw [Metric.continuousAt_iff] at hDπ_cont
  obtain ⟨δ_Dπ, hδ_Dπ_pos, hδ_Dπ⟩ := hDπ_cont ε₁ hε₁_pos
  -- Get δ_Up with B(mstar, δ_Up) ⊆ U_plus
  obtain ⟨δ_Up, hδ_Up_pos, hδ_Up_sub⟩ := Metric.isOpen_iff.mp hU_open mstar hm_in
  -- Get δ_U with B(mstar, δ_U) ⊆ U
  obtain ⟨δ_U, hδ_U_pos, hδ_U_sub⟩ := Metric.isOpen_iff.mp hU_isopen mstar hmstar_U
  -- Get δ_diff with differentiability on B(mstar, δ_diff)
  obtain ⟨δ_diff, hδ_diff_pos, hπ_diff_ball⟩ := hπ_diff_near
  -- Expansion factor: dist(πx, m*) ≤ 2·dist(x, m*), dist(x'n1, m*) ≤ (1+Ch)·R
  let M := 2 + Ch + 1
  have hM_ge3 : (3 : ℝ) ≤ M := by linarith [hCh_nn]
  -- R₀ ensures all relevant points are in B(mstar, δ_Dπ) ∩ U ∩ diff ball
  let R₀ := min (min (min δ_Up δ_U) δ_Dπ) δ_diff / (M + 1)
  have hMp1_pos : (0 : ℝ) < M + 1 := by linarith [hCh_nn]
  have hR₀_pos : (0 : ℝ) < R₀ :=
    div_pos (lt_min (lt_min (lt_min hδ_Up_pos hδ_U_pos) hδ_Dπ_pos) hδ_diff_pos) hMp1_pos
  refine ⟨R₀, hR₀_pos, ?_⟩
  intro s₀ n hsx hslx hLn_le
  -- Abbreviations
  set sn := nesterovSeqGen f η ρ s₀ n
  set x'n := sn.lookahead η
  set gn := gradient f x'n
  set en := x'n - π x'n
  set hn := stepDispOfState f η ρ sn
  set ξn := curvatureErrorOfState (↑P) π f η ρ sn
  set un1 := auxVarOfState P μ' π η (nesterovStep f η ρ sn)
  set wn := un1 - sm • ξn
  set Ln := lyapunovOfState P μ' π f η sn
  -- R₀ ≤ various δ's
  have hMp1R₀ : (M + 1) * R₀ = min (min (min δ_Up δ_U) δ_Dπ) δ_diff :=
    mul_div_cancel₀ _ (ne_of_gt hMp1_pos)
  have hR₀_le_δUp : R₀ ≤ δ_Up := by
    calc R₀ ≤ (M + 1) * R₀ :=
          le_mul_of_one_le_left (le_of_lt hR₀_pos) (by linarith [hCh_nn])
      _ = min (min (min δ_Up δ_U) δ_Dπ) δ_diff := hMp1R₀
      _ ≤ min (min δ_Up δ_U) δ_Dπ := min_le_left _ _
      _ ≤ min δ_Up δ_U := min_le_left _ _
      _ ≤ δ_Up := min_le_left _ _
  have hMR₀_lt_min : M * R₀ < min (min (min δ_Up δ_U) δ_Dπ) δ_diff := by
    linarith [hR₀_pos]
  have hMR₀_lt_δDπ : M * R₀ < δ_Dπ :=
    lt_of_lt_of_le hMR₀_lt_min
      ((min_le_left _ _).trans (min_le_right _ _))
  have hMR₀_lt_δU : M * R₀ < δ_U :=
    lt_of_lt_of_le hMR₀_lt_min
      ((min_le_left _ _).trans
        ((min_le_left _ _).trans (min_le_right _ _)))
  have hMR₀_lt_δdiff : M * R₀ < δ_diff :=
    lt_of_lt_of_le hMR₀_lt_min (min_le_right _ _)
  -- Location in U_plus and U
  have hx'n_Up : x'n ∈ U_plus :=
    hδ_Up_sub (Metric.ball_subset_ball hR₀_le_δUp hslx)
  have hx'n_U : x'n ∈ U := hU_sub (subset_closure hx'n_Up)
  have hsx_Up : sn.x ∈ U_plus :=
    hδ_Up_sub (Metric.ball_subset_ball hR₀_le_δUp hsx)
  -- Dπ bound: any z with dist(z, m*) < M·R₀ has ‖Dπ(z) - P‖ ≤ ε₁ and z ∈ U
  have hDπ_in_MR₀ : ∀ z, dist z mstar < M * R₀ →
      ‖fderiv ℝ π z - P‖ ≤ ε₁ ∧ z ∈ U := by
    intro z hz
    constructor
    · have h := hδ_Dπ (lt_trans hz hMR₀_lt_δDπ)
      rw [dist_eq_norm, ← hP_eq] at h; exact le_of_lt h
    · exact hδ_U_sub (Metric.mem_ball.mpr (lt_trans hz hMR₀_lt_δU))
  -- Coercivity at step n
  have hcoer := hcoer_bound sn hsx_Up hx'n_Up
  have hnd : normalDispOfState π η sn = en := rfl
  rw [hnd] at hcoer
  -- ‖v‖² ≤ C_coer·Ln, ‖e‖² ≤ C_coer/μ'·Ln
  have hv_sq : ‖sn.v‖ ^ 2 ≤ C_coer * Ln := by
    have := mul_nonneg (le_of_lt hμ'_pos) (sq_nonneg ‖en‖); linarith
  have he_sq : ‖en‖ ^ 2 ≤ C_coer / μ' * Ln := by
    have h1 : μ' * ‖en‖ ^ 2 ≤ C_coer * Ln := by have := sq_nonneg ‖sn.v‖; linarith
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hμ'_pos).mpr (by linarith)
  -- Ln ≥ 0
  have hLn_nn : (0 : ℝ) ≤ Ln := by
    have h1 := sq_nonneg ‖sn.v‖
    have h2 := mul_nonneg (le_of_lt hμ'_pos) (sq_nonneg ‖en‖)
    exact nonneg_of_mul_nonneg_left (by linarith) hC_coer
  -- √Ln ≤ R₀
  have hLn_sqrt : Real.sqrt Ln ≤ R₀ := by
    calc Real.sqrt Ln ≤ Real.sqrt (R₀ ^ 2) := Real.sqrt_le_sqrt hLn_le
      _ = R₀ := Real.sqrt_sq (le_of_lt hR₀_pos)
  -- Key helper: √Ln * √Ln = Ln
  have hsqrt_sq : Real.sqrt Ln * Real.sqrt Ln = Ln := Real.mul_self_sqrt hLn_nn
  -- Helper: a² ≤ C·L → a ≤ √C · √L
  have sqrt_bound : ∀ {a C L : ℝ}, 0 ≤ a → 0 ≤ C → 0 ≤ L →
      a ^ 2 ≤ C * L → a ≤ Real.sqrt C * Real.sqrt L := by
    intro a C L ha hC hL hab
    calc a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha).symm
      _ ≤ Real.sqrt (C * L) := Real.sqrt_le_sqrt hab
      _ = Real.sqrt C * Real.sqrt L := Real.sqrt_mul hC L
  -- ‖e‖ ≤ Ce·√Ln, ‖v‖ ≤ Cv·√Ln
  have he_bound : ‖en‖ ≤ Ce * Real.sqrt Ln :=
    sqrt_bound (norm_nonneg _) (div_nonneg (le_of_lt hC_coer) (le_of_lt hμ'_pos)) hLn_nn he_sq
  have hv_bound : ‖sn.v‖ ≤ Cv * Real.sqrt Ln :=
    sqrt_bound (norm_nonneg _) (le_of_lt hC_coer) hLn_nn hv_sq
  -- ‖g‖ ≤ L·‖e‖ (gradient Lipschitz + ∇f|_S = 0)
  have hgn_bound : ‖gn‖ ≤ (↑L : ℝ) * ‖en‖ := by
    have := hf_lip.dist_le_mul x'n (hU_sub (subset_closure hx'n_Up))
      (π x'n) (hS_sub_U (hπ_on_U x'n hx'n_U).1)
    rwa [hgrad_zero (π x'n) (hπ_on_U x'n hx'n_U).1, dist_zero_right, dist_eq_norm] at this
  have hg_bound : ‖gn‖ ≤ Cg * Real.sqrt Ln := by
    calc ‖gn‖ ≤ (↑L : ℝ) * ‖en‖ := hgn_bound
      _ ≤ (↑L : ℝ) * (Ce * Real.sqrt Ln) := by gcongr
      _ = Cg * Real.sqrt Ln := by ring
  -- ‖h‖ ≤ Ch·√Ln (nesterov_step_bound)
  have hhn_bound : ‖hn‖ ≤ Ch * Real.sqrt Ln := by
    change ‖stepDispOfState f η ρ sn‖ ≤ _
    unfold stepDispOfState
    calc ‖(nesterovStep f η ρ sn).lookahead η -
            sn.lookahead η‖
        ≤ η * ‖gradient f (sn.lookahead η)‖ +
          Real.sqrt η * |ρ| * (‖sn.v‖ +
          Real.sqrt η * ‖gradient f (sn.lookahead η)‖) :=
          nesterov_step_bound f η ρ sn hη_nn
      _ ≤ η * (Cg * Real.sqrt Ln) + Real.sqrt η * |ρ| *
          (Cv * Real.sqrt Ln + Real.sqrt η * (Cg * Real.sqrt Ln)) := by
          gcongr
      _ = Ch * Real.sqrt Ln := by ring
  -- ── π(x'n) ∈ B(mstar, 2R₀) ──
  have hπx'n_dist : dist (π x'n) mstar < 2 * R₀ := by
    have hd1 := Metric.mem_ball.mp hslx
    have := (hπ_on_U x'n hx'n_U).2
    have hπe : dist x'n (π x'n) ≤ dist x'n mstar :=
      this ▸ Metric.infDist_le_dist_of_mem hmstar
    linarith [dist_triangle (π x'n) x'n mstar, dist_comm (π x'n) x'n]
  -- ── x'_{n+1} ∈ B(mstar, (1+Ch)·R₀) ──
  have hx'n1_eq : (nesterovStep f η ρ sn).lookahead η = x'n + hn := by
    change (nesterovStep f η ρ sn).lookahead η =
      sn.lookahead η + ((nesterovStep f η ρ sn).lookahead η - sn.lookahead η)
    abel
  have hx'n1_dist : dist (x'n + hn) mstar < (1 + Ch) * R₀ := by
    have hd1 := Metric.mem_ball.mp hslx
    have hhn_le : ‖hn‖ ≤ Ch * R₀ :=
      le_trans hhn_bound (mul_le_mul_of_nonneg_left hLn_sqrt hCh_nn)
    linarith [dist_triangle (x'n + hn) x'n mstar,
              show dist (x'n + hn) x'n = ‖hn‖ from by rw [dist_eq_norm, add_sub_cancel_left]]
  -- Both points in Dπ-controlled region (dist < M·R₀)
  have hMR₀_ge_2R₀ : 2 * R₀ ≤ M * R₀ :=
    mul_le_mul_of_nonneg_right (by linarith [hM_ge3]) (le_of_lt hR₀_pos)
  have hMR₀_ge_1ChR₀ : (1 + Ch) * R₀ ≤ M * R₀ :=
    mul_le_mul_of_nonneg_right (by linarith [hCh_nn]) (le_of_lt hR₀_pos)
  have hπx'n_ctrl : dist (π x'n) mstar < M * R₀ := by
    linarith [hπx'n_dist]
  have hx'n_ctrl : dist x'n mstar < M * R₀ := by
    have := Metric.mem_ball.mp hslx; linarith
  have hx'n1_ctrl : dist (x'n + hn) mstar < M * R₀ := by
    linarith [hx'n1_dist]
  -- ‖Dπ(π(x'n)) - P‖ ≤ ε₁
  have hDπ_πx'n : ‖fderiv ℝ π (π x'n) - P‖ ≤ ε₁ :=
    (hDπ_in_MR₀ (π x'n) hπx'n_ctrl).1
  -- ── ‖P en‖ ≤ ε₁·‖en‖ ──
  have hPen : ‖P en‖ ≤ ε₁ * ‖en‖ :=
    proj_normal_bound P π x'n (hπ_kills_normal x'n hx'n_Up) ε₁ hDπ_πx'n
  -- ── ‖ξn‖ ≤ ε₁·‖hn‖ ──
  have hξn_bound : ‖ξn‖ ≤ ε₁ * ‖hn‖ := by
    -- First get the MVT bound
    have hmvt := xi_bound_mvt P π x'n (x'n + hn) mstar (M * R₀)
      (Metric.mem_ball.mpr hx'n_ctrl) (Metric.mem_ball.mpr hx'n1_ctrl)
      (fun z hz => hπ_diff_ball z (Metric.ball_subset_ball (le_of_lt hMR₀_lt_δdiff) hz)) ε₁
      (fun z hz => (hDπ_in_MR₀ z (Metric.mem_ball.mp hz)).1)
    -- hmvt : ‖P ((x'n + hn) - x'n) - (π (x'n + hn) - π x'n)‖ ≤ ε₁ * ‖(x'n + hn) - x'n‖
    simp only [add_sub_cancel_left] at hmvt
    -- hmvt : ‖P hn - (π (x'n + hn) - π x'n)‖ ≤ ε₁ * ‖hn‖
    -- Now show ξn equals P hn - (π(x'n+hn) - π x'n)
    suffices hsuff : (ξn : E) = P hn - (π (x'n + hn) - π x'n) by rw [hsuff]; exact hmvt
    -- ξn was set to curvatureErrorOfState, which unfolds to:
    -- e' - e - (h - P h) where e = x'n - π x'n, e' = (x'n+hn) - π(x'n+hn), h = hn
    have hξn_unfold : (ξn : E) =
        ((nesterovStep f η ρ sn).lookahead η - π ((nesterovStep f η ρ sn).lookahead η)) -
        (x'n - π x'n) -
        (((nesterovStep f η ρ sn).lookahead η - x'n) -
         P ((nesterovStep f η ρ sn).lookahead η - x'n)) := rfl
    rw [hξn_unfold, hx'n1_eq]
    abel_nf
  -- ── ‖wn‖ ≤ Cw·√Ln (via auxVar_recursion) ──
  have hwn_eq : (wn : E) = (1 - sa) • (sn.v - P sn.v) +
      sm • en - Real.sqrt η • (gn - P gn) := by
    change un1 - sm • ξn = _
    have h_av := auxVarOfState_step P μ' η ρ π f sn hρ_eq hsa_pos hη_pos hμ'_pos
    have : (un1 : E) = ((1 - sa) • (sn.v - P sn.v) + sm • en -
        Real.sqrt η • (gn - P gn)) + sm • ξn := by
      change auxVarOfState P μ' π η (nesterovStep f η ρ sn) = _; exact h_av
    rw [this]; abel
  have hwn_bound : ‖wn‖ ≤ Cw * Real.sqrt Ln := by
    rw [hwn_eq]
    have h1 : ‖(1 - sa) • (sn.v - P sn.v)‖ ≤ ‖sn.v - P sn.v‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      calc |1 - sa| * ‖sn.v - P sn.v‖ ≤ 1 * ‖sn.v - P sn.v‖ := by
            gcongr; rw [abs_le]; exact ⟨by linarith [hsa_pos], by linarith [hsa_lt1]⟩
        _ = ‖sn.v - P sn.v‖ := one_mul _
    have hPv_sub : ‖sn.v - P sn.v‖ ≤ ‖sn.v‖ := by
      rw [← Real.sqrt_sq (norm_nonneg sn.v), ← Real.sqrt_sq (norm_nonneg (sn.v - P sn.v))]
      exact Real.sqrt_le_sqrt (by have := hP_ortho sn.v; have := sq_nonneg ‖P sn.v‖; linarith)
    have hPg_sub : ‖gn - P gn‖ ≤ ‖gn‖ := by
      rw [← Real.sqrt_sq (norm_nonneg gn), ← Real.sqrt_sq (norm_nonneg (gn - P gn))]
      exact Real.sqrt_le_sqrt (by have := hP_ortho gn; have := sq_nonneg ‖P gn‖; linarith)
    calc ‖(1 - sa) • (sn.v - P sn.v) + sm • en - Real.sqrt η • (gn - P gn)‖
        ≤ ‖(1 - sa) • (sn.v - P sn.v)‖ + ‖sm • en‖ + ‖Real.sqrt η • (gn - P gn)‖ := by
          calc ‖(1 - sa) • (sn.v - P sn.v) + sm • en - Real.sqrt η • (gn - P gn)‖
              ≤ ‖(1 - sa) • (sn.v - P sn.v) + sm • en‖ +
                ‖Real.sqrt η • (gn - P gn)‖ := norm_sub_le _ _
            _ ≤ (‖(1 - sa) • (sn.v - P sn.v)‖ + ‖sm • en‖) +
                ‖Real.sqrt η • (gn - P gn)‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ‖sn.v‖ + sm * ‖en‖ + Real.sqrt η * ‖gn‖ := by
          have hsm_e : ‖sm • en‖ = sm * ‖en‖ := by
            rw [norm_smul, Real.norm_of_nonneg hsm_nn]
          have hη_g : ‖Real.sqrt η • (gn - P gn)‖ = Real.sqrt η * ‖gn - P gn‖ := by
            rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg η)]
          have hh1 : ‖(1 - sa) • (sn.v - P sn.v)‖ ≤ ‖sn.v‖ := h1.trans hPv_sub
          have hh3 : Real.sqrt η * ‖gn - P gn‖ ≤ Real.sqrt η * ‖gn‖ :=
            mul_le_mul_of_nonneg_left hPg_sub (Real.sqrt_nonneg η)
          linarith [hsm_e, hη_g, hh1, hh3]
      _ ≤ Cv * Real.sqrt Ln + sm * (Ce * Real.sqrt Ln) +
          Real.sqrt η * (Cg * Real.sqrt Ln) := by gcongr
      _ = Cw * Real.sqrt Ln := by ring
  -- ── Bound δ_curv + proj_err ──
  have hCS_wξ := real_inner_le_norm wn ξn
  -- ‖ξn‖² ≤ ε₁ · Ch² · Ln
  have hξn_sq : ‖ξn‖ ^ 2 ≤ ε₁ * Ch ^ 2 * Ln := by
    have h1 : ‖ξn‖ ≤ ε₁ * (Ch * Real.sqrt Ln) := by
      calc ‖ξn‖ ≤ ε₁ * ‖hn‖ := hξn_bound
        _ ≤ ε₁ * (Ch * Real.sqrt Ln) := by gcongr
    have h2 : ‖ξn‖ ^ 2 ≤ (ε₁ * (Ch * Real.sqrt Ln)) ^ 2 :=
      sq_le_sq' (by linarith [norm_nonneg ξn]) h1
    have h3 : (ε₁ * (Ch * Real.sqrt Ln)) ^ 2 = ε₁ ^ 2 * Ch ^ 2 * Ln := by
      calc (ε₁ * (Ch * Real.sqrt Ln)) ^ 2
          = ε₁ ^ 2 * Ch ^ 2 * (Real.sqrt Ln * Real.sqrt Ln) := by ring
        _ = ε₁ ^ 2 * Ch ^ 2 * Ln := by rw [hsqrt_sq]
    have h4 : ε₁ ^ 2 ≤ ε₁ := by
      calc ε₁ ^ 2 = ε₁ * ε₁ := sq ε₁
        _ ≤ ε₁ * 1 := mul_le_mul_of_nonneg_left hε₁_le1 (le_of_lt hε₁_pos)
        _ = ε₁ := mul_one ε₁
    calc ‖ξn‖ ^ 2 ≤ ε₁ ^ 2 * Ch ^ 2 * Ln := by linarith
      _ ≤ ε₁ * Ch ^ 2 * Ln := by
          have h5 := mul_le_mul_of_nonneg_right h4 (mul_nonneg (sq_nonneg Ch) hLn_nn)
          linarith
  -- δ_curv bound
  have hδ_curv : sm * @inner ℝ _ _ wn ξn + sm ^ 2 / 2 * ‖ξn‖ ^ 2 ≤
      ε₁ * (sm * Cw * Ch + sm ^ 2 / 2 * Ch ^ 2) * Ln := by
    have ht1 : sm * @inner ℝ _ _ wn ξn ≤ ε₁ * (sm * Cw * Ch) * Ln := by
      have h1 : sm * @inner ℝ _ _ wn ξn ≤ sm * (‖wn‖ * ‖ξn‖) :=
        mul_le_mul_of_nonneg_left hCS_wξ hsm_nn
      have h2 : ‖wn‖ * ‖ξn‖ ≤ (Cw * Real.sqrt Ln) * (ε₁ * (Ch * Real.sqrt Ln)) := by
        gcongr
        calc ‖ξn‖ ≤ ε₁ * ‖hn‖ := hξn_bound
          _ ≤ ε₁ * (Ch * Real.sqrt Ln) := by gcongr
      have h3 : (Cw * Real.sqrt Ln) * (ε₁ * (Ch * Real.sqrt Ln)) =
          ε₁ * Cw * Ch * Ln := by
        calc (Cw * Real.sqrt Ln) * (ε₁ * (Ch * Real.sqrt Ln))
            = ε₁ * Cw * Ch * (Real.sqrt Ln * Real.sqrt Ln) := by ring
          _ = ε₁ * Cw * Ch * Ln := by rw [hsqrt_sq]
      have h4 : sm * (‖wn‖ * ‖ξn‖) ≤ sm * (ε₁ * Cw * Ch * Ln) :=
        mul_le_mul_of_nonneg_left (le_trans h2 (le_of_eq h3)) hsm_nn
      calc sm * @inner ℝ _ _ wn ξn
          ≤ sm * (‖wn‖ * ‖ξn‖) := h1
        _ ≤ sm * (ε₁ * Cw * Ch * Ln) := h4
        _ = ε₁ * (sm * Cw * Ch) * Ln := by ring
    have ht2 : sm ^ 2 / 2 * ‖ξn‖ ^ 2 ≤ ε₁ * (sm ^ 2 / 2 * Ch ^ 2) * Ln := by
      have hsm2 : (0:ℝ) ≤ sm ^ 2 / 2 := div_nonneg (sq_nonneg sm) (by norm_num : (0:ℝ) ≤ 2)
      calc sm ^ 2 / 2 * ‖ξn‖ ^ 2
          ≤ sm ^ 2 / 2 * (ε₁ * Ch ^ 2 * Ln) := mul_le_mul_of_nonneg_left hξn_sq hsm2
        _ = ε₁ * (sm ^ 2 / 2 * Ch ^ 2) * Ln := by ring
    calc sm * @inner ℝ _ _ wn ξn + sm ^ 2 / 2 * ‖ξn‖ ^ 2
        ≤ ε₁ * (sm * Cw * Ch) * Ln + ε₁ * (sm ^ 2 / 2 * Ch ^ 2) * Ln :=
          add_le_add ht1 ht2
      _ = ε₁ * (sm * Cw * Ch + sm ^ 2 / 2 * Ch ^ 2) * Ln := by ring
  -- proj_err bound
  have hproj : sa * |@inner ℝ _ _ gn (P en)| ≤ ε₁ * (sa * Cg * Ce) * Ln := by
    have hCS_gPe := abs_real_inner_le_norm gn (P en)
    have h1 : ‖gn‖ * ‖P en‖ ≤ ‖gn‖ * (ε₁ * ‖en‖) :=
      mul_le_mul_of_nonneg_left hPen (norm_nonneg _)
    have h2 : ‖gn‖ * (ε₁ * ‖en‖) ≤ (Cg * Real.sqrt Ln) * (ε₁ * (Ce * Real.sqrt Ln)) := by
      gcongr
    have h3 : (Cg * Real.sqrt Ln) * (ε₁ * (Ce * Real.sqrt Ln)) = ε₁ * Cg * Ce * Ln := by
      calc (Cg * Real.sqrt Ln) * (ε₁ * (Ce * Real.sqrt Ln))
          = ε₁ * Cg * Ce * (Real.sqrt Ln * Real.sqrt Ln) := by ring
        _ = ε₁ * Cg * Ce * Ln := by rw [hsqrt_sq]
    calc sa * |@inner ℝ _ _ gn (P en)|
        ≤ sa * (ε₁ * Cg * Ce * Ln) :=
          mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hsa_pos)
      _ = ε₁ * (sa * Cg * Ce) * Ln := by ring
  -- Assembly: total ≤ ε₁·K·Ln ≤ θ·sa·Ln
  calc sm * @inner ℝ _ _ wn ξn + sm ^ 2 / 2 * ‖ξn‖ ^ 2 +
        sa * |@inner ℝ _ _ gn (P en)|
      ≤ ε₁ * (sm * Cw * Ch + sm ^ 2 / 2 * Ch ^ 2) * Ln +
        ε₁ * (sa * Cg * Ce) * Ln := add_le_add hδ_curv hproj
    _ = ε₁ * (sm * Cw * Ch + sm ^ 2 / 2 * Ch ^ 2 + sa * Cg * Ce) * Ln := by ring
    _ ≤ ε₁ * K * Ln :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (by change sm * Cw * Ch + sm ^ 2 / 2 * Ch ^ 2 + sa * Cg * Ce ≤
                  sm * Cw * Ch + sm ^ 2 / 2 * Ch ^ 2 + sa * Cg * Ce + 1; linarith)
            (le_of_lt hε₁_pos))
          hLn_nn
    _ ≤ θ * sa * Ln :=
        mul_le_mul_of_nonneg_right hε₁K_le hLn_nn


/-- Public theorem wrapper for `curvAbsorbAssemblyProof`. -/
theorem curv_absorb_assembly
    (f : E → ℝ) (L : ℝ≥0) (hL : 0 < (L : ℝ))
    (μ' : ℝ) (hμ' : 0 < μ')
    (θ : ℝ) (hθ_pos : 0 < θ)
    (η ρ : ℝ)
    (hη_pos : 0 < η)
    (hμη_lt1 : μ' * η < 1)
    (hρ_eq : ρ = (1 - Real.sqrt (μ' * η)) / (1 + Real.sqrt (μ' * η)))
    (S : Set E)
    (π : E → E)
    (P : E →L[ℝ] E)
    (hP_ortho : ∀ v : E, ‖v‖ ^ 2 = ‖P v‖ ^ 2 + ‖v - P v‖ ^ 2)
    (mstar : E) (hmstar : mstar ∈ S)
    (hP_eq : P = fderiv ℝ π mstar)
    (U_plus : Set E) (hU_open : IsOpen U_plus) (hm_in : mstar ∈ U_plus)
    (U : Set E) (hU_isopen : IsOpen U) (hU_sub : closure U_plus ⊆ U)
    (hf_lip : LipschitzOnWith L (gradient f) U)
    (hS_sub_U : S ⊆ U)
    (hmstar_U : mstar ∈ U)
    (hπ_on_U : ∀ x ∈ U, π x ∈ S ∧ dist x (π x) = Metric.infDist x S)
    (hDπ_cont : ContinuousAt (fun x => fderiv ℝ π x) mstar)
    (C_coer : ℝ) (hC_coer : 0 < C_coer)
    (hcoer_bound : ∀ (x₁ : E) (n : ℕ),
        (nesterovSeq f η ρ x₁ n).x ∈ U_plus →
        (nesterovSeq f η ρ x₁ n).lookahead η ∈ U_plus →
        ‖(nesterovSeq f η ρ x₁ n).v‖ ^ 2 +
          μ' * ‖normalDisp π f η ρ x₁ n‖ ^ 2 ≤
          C_coer * lyapunov P μ' π f η ρ x₁ n)
    (hπ_kills_normal : ∀ x ∈ U_plus, fderiv ℝ π (π x) (x - π x) = 0)
    (hgrad_zero : ∀ x ∈ S, gradient f x = 0)
    (hπ_diff_near : ∃ δ_diff > 0, ∀ z ∈ Metric.ball mstar δ_diff, DifferentiableAt ℝ π z) :
    ∃ R_abs : ℝ, 0 < R_abs ∧ ∀ (x₁ : E) (n : ℕ),
        (nesterovSeq f η ρ x₁ n).x ∈ Metric.ball mstar R_abs →
        (nesterovSeq f η ρ x₁ n).lookahead η ∈ Metric.ball mstar R_abs →
        lyapunov P μ' π f η ρ x₁ n ≤ R_abs ^ 2 →
        let sn := nesterovSeq f η ρ x₁ n
        let gn := gradient f (sn.lookahead η)
        let en := sn.lookahead η - π (sn.lookahead η)
        let ξn := curvatureError (↑P) π f η ρ x₁ n
        let un1 := auxVar P μ' π f η ρ x₁ (n + 1)
        let wn := un1 - Real.sqrt μ' • ξn
        let δ_curv := Real.sqrt μ' * @inner ℝ _ _ wn ξn +
                      (Real.sqrt μ') ^ 2 / 2 * ‖ξn‖ ^ 2
        let a := Real.sqrt (μ' * η)
        let Ln := lyapunov P μ' π f η ρ x₁ n
        let proj_err := a * abs (@inner ℝ _ _ gn (P en))
        δ_curv + proj_err ≤ θ * a * Ln := by
  exact curvAbsorbAssemblyProof (f := f) (L := L) (hL := hL) (μ' := μ') (hμ' := hμ') (θ := θ)
    (hθ_pos := hθ_pos) (η := η) (ρ := ρ) (hη_pos := hη_pos) (hμη_lt1 := hμη_lt1) (hρ_eq := hρ_eq)
    (S := S) (π := π) (P := P) (hP_ortho := hP_ortho) (mstar := mstar) (hmstar := hmstar)
    (hP_eq := hP_eq) (U_plus := U_plus) (hU_open := hU_open) (hm_in := hm_in) (U := U)
    (hU_isopen := hU_isopen) (hU_sub := hU_sub) (hf_lip := hf_lip) (hS_sub_U := hS_sub_U)
    (hmstar_U := hmstar_U) (hπ_on_U := hπ_on_U) (hDπ_cont := hDπ_cont) (C_coer := C_coer)
    (hC_coer := hC_coer) (hcoer_bound := hcoer_bound) (hπ_kills_normal := hπ_kills_normal)
    (hgrad_zero := hgrad_zero) (hπ_diff_near := hπ_diff_near)

/-- Public theorem wrapper for `curvAbsorbAssemblyGenProof`. -/
theorem curv_absorb_assembly_gen
    (f : E → ℝ) (L : ℝ≥0) (hL : 0 < (L : ℝ))
    (μ' : ℝ) (hμ' : 0 < μ')
    (θ : ℝ) (hθ_pos : 0 < θ)
    (η ρ : ℝ)
    (hη_pos : 0 < η)
    (hμη_lt1 : μ' * η < 1)
    (hρ_eq : ρ = (1 - Real.sqrt (μ' * η)) / (1 + Real.sqrt (μ' * η)))
    (S : Set E)
    (π : E → E)
    (P : E →L[ℝ] E)
    (hP_ortho : ∀ v : E, ‖v‖ ^ 2 = ‖P v‖ ^ 2 + ‖v - P v‖ ^ 2)
    (mstar : E) (hmstar : mstar ∈ S)
    (hP_eq : P = fderiv ℝ π mstar)
    (U_plus : Set E) (hU_open : IsOpen U_plus) (hm_in : mstar ∈ U_plus)
    (U : Set E) (hU_isopen : IsOpen U) (hU_sub : closure U_plus ⊆ U)
    (hf_lip : LipschitzOnWith L (gradient f) U)
    (hS_sub_U : S ⊆ U)
    (hmstar_U : mstar ∈ U)
    (hπ_on_U : ∀ x ∈ U, π x ∈ S ∧ dist x (π x) = Metric.infDist x S)
    (hDπ_cont : ContinuousAt (fun x => fderiv ℝ π x) mstar)
    (C_coer : ℝ) (hC_coer : 0 < C_coer)
    (hcoer_bound : ∀ (s : NesterovState d),
        s.x ∈ U_plus →
        s.lookahead η ∈ U_plus →
        ‖s.v‖ ^ 2 +
          μ' * ‖normalDispOfState π η s‖ ^ 2 ≤
          C_coer * lyapunovOfState P μ' π f η s)
    (hπ_kills_normal : ∀ x ∈ U_plus, fderiv ℝ π (π x) (x - π x) = 0)
    (hgrad_zero : ∀ x ∈ S, gradient f x = 0)
    (hπ_diff_near : ∃ δ_diff > 0, ∀ z ∈ Metric.ball mstar δ_diff, DifferentiableAt ℝ π z) :
    ∃ R_abs : ℝ, 0 < R_abs ∧ ∀ (s₀ : NesterovState d) (n : ℕ),
        (nesterovSeqGen f η ρ s₀ n).x ∈ Metric.ball mstar R_abs →
        (nesterovSeqGen f η ρ s₀ n).lookahead η ∈ Metric.ball mstar R_abs →
        lyapunovOfState P μ' π f η (nesterovSeqGen f η ρ s₀ n) ≤ R_abs ^ 2 →
        let sn := nesterovSeqGen f η ρ s₀ n
        let gn := gradient f (sn.lookahead η)
        let en := sn.lookahead η - π (sn.lookahead η)
        let ξn := curvatureErrorOfState (↑P) π f η ρ sn
        let un1 := auxVarOfState P μ' π η (nesterovStep f η ρ sn)
        let wn := un1 - Real.sqrt μ' • ξn
        let δ_curv := Real.sqrt μ' * @inner ℝ _ _ wn ξn +
                      (Real.sqrt μ') ^ 2 / 2 * ‖ξn‖ ^ 2
        let a := Real.sqrt (μ' * η)
        let Ln := lyapunovOfState P μ' π f η sn
        let proj_err := a * abs (@inner ℝ _ _ gn (P en))
        δ_curv + proj_err ≤ θ * a * Ln := by
  exact curvAbsorbAssemblyGenProof (f := f) (L := L) (hL := hL) (μ' := μ') (hμ' := hμ') (θ := θ)
    (hθ_pos := hθ_pos) (η := η) (ρ := ρ) (hη_pos := hη_pos) (hμη_lt1 := hμη_lt1) (hρ_eq := hρ_eq)
    (S := S) (π := π) (P := P) (hP_ortho := hP_ortho) (mstar := mstar) (hmstar := hmstar)
    (hP_eq := hP_eq) (U_plus := U_plus) (hU_open := hU_open) (hm_in := hm_in) (U := U)
    (hU_isopen := hU_isopen) (hU_sub := hU_sub) (hf_lip := hf_lip) (hS_sub_U := hS_sub_U)
    (hmstar_U := hmstar_U) (hπ_on_U := hπ_on_U) (hDπ_cont := hDπ_cont) (C_coer := C_coer)
    (hC_coer := hC_coer) (hcoer_bound := hcoer_bound) (hπ_kills_normal := hπ_kills_normal)
    (hgrad_zero := hgrad_zero) (hπ_diff_near := hπ_diff_near)

end PLAcceleratedNesterovLean
