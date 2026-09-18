/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanPool.PLAcceleratedNesterovLean.Core.NesterovSeqGen
import LeanPool.PLAcceleratedNesterovLean.Convergence.CurvAbsorb.Algebraic
import LeanPool.PLAcceleratedNesterovLean.Convergence.StateContraction.AuxVarRecursion

/-!
# Curvature Absorption Assembly

Standalone proof that the curvature + projector-freezing perturbation is absorbable.
Extracted from the main theorem to keep its proof term small (avoids kernel slowdown).

The key idea: Dπ is continuous at m⋆, so for small enough R,
all perturbation terms are O(ε₁ · Ln) with ε₁ = sup ‖Dπ-P‖ → 0.
-/

@[expose] public section

open scoped NNReal
noncomputable section

namespace PLAcceleratedNesterovLean


variable {d : ℕ}
-- Notation for ℝ^d
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem leSqrtMulSqrtOfSquareLe {a C L : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hab : a ^ 2 ≤ C * L) : a ≤ Real.sqrt C * Real.sqrt L := by
  calc a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha).symm
    _ ≤ Real.sqrt (C * L) := Real.sqrt_le_sqrt hab
    _ = Real.sqrt C * Real.sqrt L := Real.sqrt_mul hC L

private theorem existsScaledRadius (a b c e M : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e) (hM : 1 ≤ M) :
    ∃ radius > 0, radius ≤ a ∧ M * radius < b ∧ M * radius < c ∧ M * radius < e := by
  let δ := min (min (min a b) c) e
  have hδ : 0 < δ := lt_min (lt_min (lt_min ha hb) hc) he
  have hden : 0 < M + 1 := by linarith
  let radius := δ / (M + 1)
  have hradius : 0 < radius := div_pos hδ hden
  have hscaled : (M + 1) * radius = δ := mul_div_cancel₀ _ (ne_of_gt hden)
  have hsmall : M * radius < δ := by nlinarith
  have hle : radius ≤ δ := div_le_self (le_of_lt hδ) (by linarith)
  have hδa : δ ≤ a := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδb : δ ≤ b := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδc : δ ≤ c := (min_le_left _ _).trans (min_le_right _ _)
  exact ⟨radius, hradius, hle.trans hδa, hsmall.trans_le hδb, hsmall.trans_le hδc,
    hsmall.trans_le (min_le_right _ _)⟩

private theorem orthogonalCombinationBound (P : E →L[ℝ] E)
    (hP_ortho : ∀ v : E, ‖v‖ ^ 2 = ‖P v‖ ^ 2 + ‖v - P v‖ ^ 2)
    (v en gn : E) (sm sa η Cv Ce Cg Ln : ℝ)
    (hsm_nn : 0 ≤ sm) (hsa_pos : 0 < sa) (hsa_lt1 : sa < 1)
    (hv_bound : ‖v‖ ≤ Cv * Real.sqrt Ln)
    (he_bound : ‖en‖ ≤ Ce * Real.sqrt Ln)
    (hg_bound : ‖gn‖ ≤ Cg * Real.sqrt Ln) :
    ‖(1 - sa) • (v - P v) + sm • en - Real.sqrt η • (gn - P gn)‖ ≤
      (Cv + sm * Ce + Real.sqrt η * Cg) * Real.sqrt Ln := by
  have h1 : ‖(1 - sa) • (v - P v)‖ ≤ ‖v - P v‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |1 - sa| * ‖v - P v‖ ≤ 1 * ‖v - P v‖ := by
          gcongr; rw [abs_le]; exact ⟨by linarith [hsa_pos], by linarith [hsa_lt1]⟩
      _ = ‖v - P v‖ := one_mul _
  have hPv_sub : ‖v - P v‖ ≤ ‖v‖ := by
    rw [← Real.sqrt_sq (norm_nonneg v), ← Real.sqrt_sq (norm_nonneg (v - P v))]
    exact Real.sqrt_le_sqrt (by have := hP_ortho v; have := sq_nonneg ‖P v‖; linarith)
  have hPg_sub : ‖gn - P gn‖ ≤ ‖gn‖ := by
    rw [← Real.sqrt_sq (norm_nonneg gn), ← Real.sqrt_sq (norm_nonneg (gn - P gn))]
    exact Real.sqrt_le_sqrt (by have := hP_ortho gn; have := sq_nonneg ‖P gn‖; linarith)
  calc ‖(1 - sa) • (v - P v) + sm • en - Real.sqrt η • (gn - P gn)‖
      ≤ ‖(1 - sa) • (v - P v)‖ + ‖sm • en‖ + ‖Real.sqrt η • (gn - P gn)‖ := by
        calc ‖(1 - sa) • (v - P v) + sm • en - Real.sqrt η • (gn - P gn)‖
            ≤ ‖(1 - sa) • (v - P v) + sm • en‖ +
              ‖Real.sqrt η • (gn - P gn)‖ := norm_sub_le _ _
          _ ≤ (‖(1 - sa) • (v - P v)‖ + ‖sm • en‖) +
              ‖Real.sqrt η • (gn - P gn)‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ‖v‖ + sm * ‖en‖ + Real.sqrt η * ‖gn‖ := by
        have hsm_e : ‖sm • en‖ = sm * ‖en‖ := by
          rw [norm_smul, Real.norm_of_nonneg hsm_nn]
        have hη_g : ‖Real.sqrt η • (gn - P gn)‖ = Real.sqrt η * ‖gn - P gn‖ := by
          rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg η)]
        have hh1 : ‖(1 - sa) • (v - P v)‖ ≤ ‖v‖ := h1.trans hPv_sub
        have hh3 : Real.sqrt η * ‖gn - P gn‖ ≤ Real.sqrt η * ‖gn‖ :=
          mul_le_mul_of_nonneg_left hPg_sub (Real.sqrt_nonneg η)
        linarith [hsm_e, hη_g, hh1, hh3]
    _ ≤ Cv * Real.sqrt Ln + sm * (Ce * Real.sqrt Ln) +
        Real.sqrt η * (Cg * Real.sqrt Ln) := by gcongr
    _ = (Cv + sm * Ce + Real.sqrt η * Cg) * Real.sqrt Ln := by ring

/-- A common radius controls the curvature error uniformly over any family of states
satisfying the same coercivity bound. -/
private theorem curvAbsorbAssemblyFamily {ι : Type*}
    (states : ι → NesterovState d)
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
    (hcoer_bound : ∀ i,
        (states i).x ∈ U_plus →
        (states i).lookahead η ∈ U_plus →
        ‖(states i).v‖ ^ 2 +
          μ' * ‖normalDispOfState π η (states i)‖ ^ 2 ≤
          C_coer * lyapunovOfState P μ' π f η (states i))
    (hπ_kills_normal : ∀ x ∈ U_plus, fderiv ℝ π (π x) (x - π x) = 0)
    (hgrad_zero : ∀ x ∈ S, gradient f x = 0)
    (hπ_diff_near : ∃ δ_diff > 0, ∀ z ∈ Metric.ball mstar δ_diff, DifferentiableAt ℝ π z) :
    ∃ R_abs : ℝ, 0 < R_abs ∧ ∀ i,
        (states i).x ∈ Metric.ball mstar R_abs →
        (states i).lookahead η ∈ Metric.ball mstar R_abs →
        lyapunovOfState P μ' π f η (states i) ≤ R_abs ^ 2 →
        let sn := states i
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
  set sm := Real.sqrt μ'
  set sa := Real.sqrt (μ' * η)
  have hsm_pos : (0 : ℝ) < sm := Real.sqrt_pos_of_pos hμ'
  have hsm_nn : (0 : ℝ) ≤ sm := le_of_lt hsm_pos
  have hsa_pos : (0 : ℝ) < sa := Real.sqrt_pos_of_pos (mul_pos hμ' hη_pos)
  have hsa_lt1 : sa < 1 := by
    calc sa < Real.sqrt 1 := Real.sqrt_lt_sqrt (le_of_lt (mul_pos hμ' hη_pos)) hμη_lt1
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
  let K := (sm ^ 2 * Cw ^ 2 + Ch ^ 2) / 2 + sm ^ 2 / 2 * Ch ^ 2 + sa * Cg * Ce + 1
  have hK_pos : (0 : ℝ) < K := by
    dsimp [K]
    positivity
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
  obtain ⟨R₀, hR₀_pos, hR₀_le_δUp, hMR₀_lt_δU, hMR₀_lt_δDπ, hMR₀_lt_δdiff⟩ :=
    existsScaledRadius δ_Up δ_U δ_Dπ δ_diff M hδ_Up_pos hδ_U_pos hδ_Dπ_pos hδ_diff_pos
      (by linarith)
  refine ⟨R₀, hR₀_pos, ?_⟩
  intro i hsx hslx hLn_le
  -- Abbreviations
  set sn := states i
  set x'n := sn.lookahead η
  set gn := gradient f x'n
  set en := x'n - π x'n
  set hn := stepDispOfState f η ρ sn
  set ξn := curvatureErrorOfState (↑P) π f η ρ sn
  set un1 := auxVarOfState P μ' π η (nesterovStep f η ρ sn)
  set wn := un1 - sm • ξn
  set Ln := lyapunovOfState P μ' π f η sn
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
  have hcoer := hcoer_bound i hsx_Up hx'n_Up
  have hnd : normalDispOfState π η sn = en := rfl
  rw [hnd] at hcoer
  -- ‖v‖² ≤ C_coer·Ln, ‖e‖² ≤ C_coer/μ'·Ln
  have hv_sq : ‖sn.v‖ ^ 2 ≤ C_coer * Ln := by
    have := mul_nonneg (le_of_lt hμ') (sq_nonneg ‖en‖); linarith
  have he_sq : ‖en‖ ^ 2 ≤ C_coer / μ' * Ln := by
    have h1 : μ' * ‖en‖ ^ 2 ≤ C_coer * Ln := by have := sq_nonneg ‖sn.v‖; linarith
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hμ').mpr (by linarith)
  -- Ln ≥ 0
  have hLn_nn : (0 : ℝ) ≤ Ln := by
    have h1 := sq_nonneg ‖sn.v‖
    have h2 := mul_nonneg (le_of_lt hμ') (sq_nonneg ‖en‖)
    exact nonneg_of_mul_nonneg_left (by linarith) hC_coer
  -- √Ln ≤ R₀
  have hLn_sqrt : Real.sqrt Ln ≤ R₀ := by
    calc Real.sqrt Ln ≤ Real.sqrt (R₀ ^ 2) := Real.sqrt_le_sqrt hLn_le
      _ = R₀ := Real.sqrt_sq (le_of_lt hR₀_pos)
  -- Key helper: √Ln * √Ln = Ln
  have hsqrt_sq : Real.sqrt Ln * Real.sqrt Ln = Ln := Real.mul_self_sqrt hLn_nn
  -- Helper: a² ≤ C·L → a ≤ √C · √L
  -- ‖e‖ ≤ Ce·√Ln, ‖v‖ ≤ Cv·√Ln
  have he_bound : ‖en‖ ≤ Ce * Real.sqrt Ln :=
    leSqrtMulSqrtOfSquareLe (norm_nonneg _) (div_nonneg (le_of_lt hC_coer) (le_of_lt hμ')) he_sq
  have hv_bound : ‖sn.v‖ ≤ Cv * Real.sqrt Ln :=
    leSqrtMulSqrtOfSquareLe (norm_nonneg _) (le_of_lt hC_coer) hv_sq
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
    have h_av := auxVarOfState_step P μ' η ρ π f sn hρ_eq hsa_pos hη_pos hμ'
    have : (un1 : E) = ((1 - sa) • (sn.v - P sn.v) + sm • en -
        Real.sqrt η • (gn - P gn)) + sm • ξn := by
      change auxVarOfState P μ' π η (nesterovStep f η ρ sn) = _; exact h_av
    rw [this]; abel
  have hwn_bound : ‖wn‖ ≤ Cw * Real.sqrt Ln := by
    rw [hwn_eq]
    exact orthogonalCombinationBound P hP_ortho sn.v en gn sm sa η Cv Ce Cg Ln
      hsm_nn hsa_pos hsa_lt1 hv_bound he_bound hg_bound
  have square_bound {v : E} {C : ℝ} (h : ‖v‖ ≤ C * Real.sqrt Ln) :
      ‖v‖ ^ 2 ≤ C ^ 2 * Ln := by
    calc ‖v‖ ^ 2 ≤ (C * Real.sqrt Ln) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h _
      _ = C ^ 2 * Ln := by rw [mul_pow, Real.sq_sqrt hLn_nn]
  have hwh : sm ^ 2 * ‖wn‖ ^ 2 + ‖hn‖ ^ 2 ≤ (sm ^ 2 * Cw ^ 2 + Ch ^ 2) * Ln := by
    calc sm ^ 2 * ‖wn‖ ^ 2 + ‖hn‖ ^ 2 ≤
        sm ^ 2 * (Cw ^ 2 * Ln) + Ch ^ 2 * Ln :=
          add_le_add (mul_le_mul_of_nonneg_left (square_bound hwn_bound) (sq_nonneg sm))
            (square_bound hhn_bound)
      _ = (sm ^ 2 * Cw ^ 2 + Ch ^ 2) * Ln := by ring
  have hge : ‖gn‖ * ‖en‖ ≤ (Cg * Ce) * Ln := by
    calc ‖gn‖ * ‖en‖ ≤ (Cg * Real.sqrt Ln) * (Ce * Real.sqrt Ln) := by gcongr
      _ = (Cg * Ce) * (Real.sqrt Ln * Real.sqrt Ln) := by ring
      _ = (Cg * Ce) * Ln := by rw [hsqrt_sq]
  apply curv_absorption_algebraic wn ξn gn (P en) hn en sm sa Ln hsm_nn hsa_pos hLn_nn
    ε₁ hε₁_pos hε₁_le1 hξn_bound hPen (sm ^ 2 * Cw ^ 2 + Ch ^ 2) (by positivity) hwh
    (Ch ^ 2) (sq_nonneg _) (square_bound hhn_bound) (Cg * Ce) (mul_nonneg hCg_nn hCe_nn)
    hge θ hθ_pos
  apply le_trans (mul_le_mul_of_nonneg_left (show _ ≤ K from ?_) (le_of_lt hε₁_pos)) hε₁K_le
  dsimp [K]
  linarith

/-- A uniform curvature-absorption radius for Nesterov sequences with zero initial velocity. -/
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
  obtain ⟨R_abs, hR_abs, hbound⟩ := curvAbsorbAssemblyFamily
    (states := fun (index : E × ℕ) ↦ nesterovSeq f η ρ index.1 index.2)
    (f := f) (L := L) (hL := hL) (μ' := μ') (hμ' := hμ') (θ := θ)
    (hθ_pos := hθ_pos) (η := η) (ρ := ρ) (hη_pos := hη_pos) (hμη_lt1 := hμη_lt1) (hρ_eq := hρ_eq)
    (S := S) (π := π) (P := P) (hP_ortho := hP_ortho) (mstar := mstar) (hmstar := hmstar)
    (hP_eq := hP_eq) (U_plus := U_plus) (hU_open := hU_open) (hm_in := hm_in) (U := U)
    (hU_isopen := hU_isopen) (hU_sub := hU_sub) (hf_lip := hf_lip) (hS_sub_U := hS_sub_U)
    (hmstar_U := hmstar_U) (hπ_on_U := hπ_on_U) (hDπ_cont := hDπ_cont) (C_coer := C_coer)
    (hC_coer := hC_coer) (hcoer_bound := fun index ↦ hcoer_bound index.1 index.2)
    (hπ_kills_normal := hπ_kills_normal)
    (hgrad_zero := hgrad_zero) (hπ_diff_near := hπ_diff_near)
  refine ⟨R_abs, hR_abs, ?_⟩
  intro x₁ n
  exact hbound (x₁, n)

/-- A uniform curvature-absorption radius for Nesterov sequences with arbitrary initial state. -/
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
  obtain ⟨R_abs, hR_abs, hbound⟩ := curvAbsorbAssemblyFamily
    (states := fun (state : NesterovState d) ↦ state)
    (f := f) (L := L) (hL := hL) (μ' := μ') (hμ' := hμ') (θ := θ)
    (hθ_pos := hθ_pos) (η := η) (ρ := ρ) (hη_pos := hη_pos) (hμη_lt1 := hμη_lt1) (hρ_eq := hρ_eq)
    (S := S) (π := π) (P := P) (hP_ortho := hP_ortho) (mstar := mstar) (hmstar := hmstar)
    (hP_eq := hP_eq) (U_plus := U_plus) (hU_open := hU_open) (hm_in := hm_in) (U := U)
    (hU_isopen := hU_isopen) (hU_sub := hU_sub) (hf_lip := hf_lip) (hS_sub_U := hS_sub_U)
    (hmstar_U := hmstar_U) (hπ_on_U := hπ_on_U) (hDπ_cont := hDπ_cont) (C_coer := C_coer)
    (hC_coer := hC_coer) (hcoer_bound := hcoer_bound) (hπ_kills_normal := hπ_kills_normal)
    (hgrad_zero := hgrad_zero) (hπ_diff_near := hπ_diff_near)
  refine ⟨R_abs, hR_abs, ?_⟩
  intro s₀ n
  exact hbound (nesterovSeqGen f η ρ s₀ n)

end PLAcceleratedNesterovLean
