/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import LeanPool.PLAcceleratedNesterovLean.Convergence.Coercivity.Step1
import LeanPool.PLAcceleratedNesterovLean.Convergence.Coercivity.Step2
import LeanPool.PLAcceleratedNesterovLean.Convergence.Coercivity.Core
import LeanPool.PLAcceleratedNesterovLean.Core.NesterovSeqGen

/-!
# Lyapunov Coercivity

The Lyapunov function L_n controls the physical quantities ‖v_n‖² + μ'‖e_n‖²
and the potential Ψ(x_n). The constants depend only on a = √(μ'·η).
-/

noncomputable section

namespace PLAcceleratedNesterovLean

open scoped Topology NNReal
open Manifold

/-- **State-based coercivity of the Lyapunov function.**

Whenever x_n, x'_n ∈ Ω, the Lyapunov function controls:
  (1) ‖v_n‖² + μ'‖e_n‖² ≤ C_coer · L_n
  (2) Ψ(x_n) ≤ C_Ψ · L_n

This version is state-based: it quantifies over arbitrary `NesterovState`s
rather than sequence indices. -/
theorem lyapunov_coercivity_gen
    {d : ℕ} (_hd : 0 < d)
    -- The objective function
    (f : E d → ℝ)
    -- Parameters
    (L : ℝ≥0) (_hL : 0 < (L : ℝ))
    (μ' : ℝ) (hμ' : 0 < μ')
    (η : ℝ) (_hη : η = 1 / (L : ℝ)) (hη_pos : 0 < η)
    (hμη_lt1 : μ' * η < 1)
    -- S = argmin set
    (S : Set (E d))
    (_hM_argmin : S = argminSet f)
    -- Nearest-point projection
    (π : E d → E d)
    (_hπ_proj : ∀ x ∈ S, π x = x)
    (hπ_in_S : ∀ x, π x ∈ S)
    -- Tangent projector P at the fixed base point m⋆
    (P : E d →L[ℝ] E d)
    -- P is an orthogonal projector (idempotent + self-adjoint)
    (_hP_idem : ∀ x : E d, P (P x) = P x)
    (_hP_self_adj : ∀ x y : E d, @inner ℝ _ _ (P x) y = @inner ℝ _ _ x (P y))
    -- Orthogonal decomposition (follows from hP_idem + hP_self_adj)
    (hP_ortho : ∀ v : E d, ‖v‖ ^ 2 = ‖P v‖ ^ 2 + ‖v - P v‖ ^ 2)
    -- Neighborhood Ω where we work
    (Ω : Set (E d))
    (hπ_metric : ∀ x ∈ Ω, dist x (π x) = Metric.infDist x S)
    -- Quadratic growth on Ω (from `local_fiberwise_geometry`)
    (hQG : ∀ x ∈ Ω, f x - fStar f ≥ μ' / 2 * (Metric.infDist x S) ^ 2) :
    -- Conclusion: ∃ constants C_coer, C_Ψ depending only on a = √(μ'η)
    ∃ (C_coer C_Ψ : ℝ), 0 < C_coer ∧ 0 < C_Ψ ∧
      ∀ (s : NesterovState d),
        let Ln := lyapunovOfState P μ' π f η s
        s.x ∈ Ω →
        s.lookahead η ∈ Ω →
        -- (1) Velocity and error control
        ‖s.v‖ ^ 2 + μ' * ‖normalDispOfState π η s‖ ^ 2 ≤ C_coer * Ln ∧
        -- (2) Ψ control
        psi f μ' S s.x ≤ C_Ψ * Ln := by
  -- Set a = √(μ'η) and prove 0 ≤ a < 1
  set a := Real.sqrt (μ' * η) with ha_def
  have ha_nn : (0 : ℝ) ≤ a := Real.sqrt_nonneg _
  have ha_lt1 : a < 1 := by
    calc a < Real.sqrt 1 :=
          Real.sqrt_lt_sqrt (le_of_lt (mul_pos hμ' hη_pos)) hμη_lt1
      _ = 1 := Real.sqrt_one
  have h1a : (0 : ℝ) < 1 - a := by linarith
  have h1a_sq : (0 : ℝ) < (1 - a) ^ 2 := pow_pos h1a 2
  -- C_coer = 60/(1-a)², C_Ψ = 2
  refine ⟨60 / (1 - a) ^ 2, 2, div_pos (by norm_num) h1a_sq, two_pos, ?_⟩
  intro s Ln hx hx'
  constructor
  · -- (1) ‖v_n‖² + μ'·‖e_n‖² ≤ C_coer · L_n
    -- Abbreviations
    set EE := ‖normalDispOfState π η s‖ with hE_def
    set U := ‖auxVarOfState P μ' π η s‖ with hU_def
    set T := ‖P s.v‖ with hT_def
    set A := ‖s.v - P s.v‖ with hA_def
    set D := Metric.infDist s.x S with hD_def
    -- Non-negativity
    have hE_nn : 0 ≤ EE := norm_nonneg _
    have hU_nn : 0 ≤ U := norm_nonneg _
    have hT_nn : 0 ≤ T := norm_nonneg _
    have hA_nn : 0 ≤ A := norm_nonneg _
    have hD_nn : 0 ≤ D := Metric.infDist_nonneg
    have hV_nn : 0 ≤ ‖s.v‖ := norm_nonneg _
    -- Lyapunov setup
    have hlam_pos : 0 < (1 + a) ^ 2 / (2 * (1 - a)) :=
      div_pos (by positivity) (by linarith)
    have hgap_nn : 0 ≤ f s.x - fStar f := by
      linarith [hQG s.x hx,
        mul_nonneg (div_nonneg (le_of_lt hμ') two_pos.le)
          (sq_nonneg (Metric.infDist s.x S))]
    -- Lyapunov bounds
    have hgap_le : f s.x - fStar f ≤ Ln :=
      lyapunov_gap_bound (f s.x - fStar f) (U ^ 2) ((1 + a) ^ 2 / (2 * (1 - a)))
        (T ^ 2) Ln hgap_nn (sq_nonneg _) hlam_pos (sq_nonneg _) rfl
    have hu_le : U ^ 2 ≤ 2 * Ln :=
      lyapunov_u_bound (f s.x - fStar f) (U ^ 2) ((1 + a) ^ 2 / (2 * (1 - a)))
        (T ^ 2) Ln hgap_nn (sq_nonneg _) hlam_pos (sq_nonneg _) rfl
    have hLn_nn : 0 ≤ Ln := by linarith [hu_le, sq_nonneg U]
    have hPv_le : T ^ 2 ≤ 2 * Ln := by
      have hlam_ge : (1 : ℝ) / 2 ≤ (1 + a) ^ 2 / (2 * (1 - a)) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by linarith : (0 : ℝ) < 2 * (1 - a))]
        nlinarith [sq_nonneg a]
      have hPv_bound := lyapunov_Pv_bound (f s.x - fStar f) (U ^ 2)
        ((1 + a) ^ 2 / (2 * (1 - a))) (T ^ 2) Ln hgap_nn (sq_nonneg _) hlam_pos (sq_nonneg _) rfl
      calc T ^ 2 ≤ Ln / ((1 + a) ^ 2 / (2 * (1 - a))) := hPv_bound
        _ ≤ Ln / (1 / 2) := by
            apply div_le_div_of_nonneg_left hLn_nn (by norm_num : (0 : ℝ) < 1 / 2) hlam_ge
        _ = 2 * Ln := by ring
    -- QG at x_n: μ'·D² ≤ 2Ln
    have hD_sq : μ' * D ^ 2 ≤ 2 * Ln := by nlinarith [hQG s.x hx]
    -- A ≤ U + √μ'·E  (from u = P⊥v + √μ'·e)
    have hperp : A ≤ U + Real.sqrt μ' * EE := by
      have h := perp_v_bound_from_u (auxVarOfState P μ' π η s)
        (s.v - P s.v) (normalDispOfState π η s) (Real.sqrt μ') rfl
      rwa [abs_of_nonneg (Real.sqrt_nonneg μ')] at h
    -- E ≤ D + √η·‖v‖  (triangle inequality)
    have hE_tri : EE ≤ D + Real.sqrt η * ‖s.v‖ := by
      have h_eq : EE = Metric.infDist (s.lookahead η) S := by
        change ‖s.lookahead η - π (s.lookahead η)‖ = _
        rw [← dist_eq_norm, hπ_metric (s.lookahead η) hx']
      have h_le : Metric.infDist (s.lookahead η) S ≤ ‖s.lookahead η - π s.x‖ := by
        rw [← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem (hπ_in_S s.x)
      have h_tri : ‖s.lookahead η - π s.x‖ ≤ D + Real.sqrt η * ‖s.v‖ := by
        change ‖(s.x + Real.sqrt η • s.v) - π s.x‖ ≤ _
        calc ‖(s.x + Real.sqrt η • s.v) - π s.x‖
            = ‖(s.x - π s.x) + Real.sqrt η • s.v‖ := by congr 1; abel
          _ ≤ ‖s.x - π s.x‖ + ‖Real.sqrt η • s.v‖ := norm_add_le _ _
          _ = ‖s.x - π s.x‖ + Real.sqrt η * ‖s.v‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg η)]
          _ = dist s.x (π s.x) + Real.sqrt η * ‖s.v‖ := by rw [dist_eq_norm]
          _ = D + Real.sqrt η * ‖s.v‖ := by rw [hD_def, hπ_metric s.x hx]
      linarith
    -- ‖v‖ ≤ A + T  (triangle)
    have hV_ub : ‖s.v‖ ≤ A + T := by
      have := norm_add_le (s.v - P s.v) (P s.v)
      simp only [sub_add_cancel] at this; exact this
    -- ‖v‖² = T² + A²  (orthogonal decomposition)
    have hv_ortho : ‖s.v‖ ^ 2 = T ^ 2 + A ^ 2 := hP_ortho s.v
    -- √μ' · √η = a
    have hsqrt_mul : Real.sqrt μ' * Real.sqrt η = a := by
      rw [ha_def, ← Real.sqrt_mul (le_of_lt hμ')]
    have hsq_mu : (Real.sqrt μ') ^ 2 = μ' := Real.sq_sqrt (le_of_lt hμ')
    have hsq_eta : (Real.sqrt η) ^ 2 = η := Real.sq_sqrt (le_of_lt hη_pos)
    -- Apply the core arithmetic lemma
    have hcore := coercivity_core_bound T A U EE D ‖s.v‖ (Real.sqrt μ') (Real.sqrt η) a μ' Ln
      ha_nn ha_lt1 hμ' (Real.sqrt_nonneg μ') (Real.sqrt_nonneg η)
      hsq_mu hsqrt_mul hE_nn hU_nn hT_nn hA_nn hD_nn hV_nn
      hPv_le hu_le hD_sq hv_ortho hperp hE_tri hV_ub
    -- Convert: goal is ‖v‖²+μ'E² ≤ 60/(1-a)²·Ln, i.e., (1-a)²(‖v‖²+μ'E²) ≤ 60Ln
    rw [div_mul_eq_mul_div, le_div_iff₀ h1a_sq]
    linarith [hcore]
  · -- (2) Ψ(x_n) ≤ 2 · L_n
    have hqg := hQG s.x hx
    have hgap_nn : 0 ≤ f s.x - fStar f := by
      have := mul_nonneg (div_nonneg (le_of_lt hμ') two_pos.le)
        (sq_nonneg (Metric.infDist s.x S))
      linarith
    have hlam_pos : 0 < (1 + a) ^ 2 / (2 * (1 - a)) :=
      div_pos (by positivity) (by linarith)
    have hpsi_le : psi f μ' S s.x ≤ 2 * (f s.x - fStar f) := by
      simp only [psi]; linarith
    have hgap_le_Ln : f s.x - fStar f ≤ Ln :=
      lyapunov_gap_bound (f s.x - fStar f) (‖auxVarOfState P μ' π η s‖ ^ 2)
        ((1 + a) ^ 2 / (2 * (1 - a)))
        (‖P s.v‖ ^ 2) Ln
        hgap_nn (sq_nonneg _) hlam_pos (sq_nonneg _) rfl
    linarith

/-- **Coercivity of the Lyapunov function.**

Whenever x_n, x'_n ∈ Ω, the Lyapunov function controls:
  (1) ‖v_n‖² + μ'‖e_n‖² ≤ C_coer · L_n
  (2) Ψ(x_n) ≤ C_Ψ · L_n
-/
theorem lyapunov_coercivity
    {d : ℕ} (_hd : 0 < d)
    -- The objective function
    (f : E d → ℝ)
    -- Parameters
    (L : ℝ≥0) (_hL : 0 < (L : ℝ))
    (μ' : ℝ) (hμ' : 0 < μ')
    (η : ℝ) (_hη : η = 1 / (L : ℝ)) (hη_pos : 0 < η)
    (hμη_lt1 : μ' * η < 1)
    (ρ : ℝ) (_hρ : ρ = (1 - Real.sqrt (μ' * η)) / (1 + Real.sqrt (μ' * η)))
    -- S = argmin set
    (S : Set (E d))
    (_hM_argmin : S = argminSet f)
    -- Nearest-point projection
    (π : E d → E d)
    (_hπ_proj : ∀ x ∈ S, π x = x)
    (hπ_in_S : ∀ x, π x ∈ S)
    -- Tangent projector P at the fixed base point m⋆
    (P : E d →L[ℝ] E d)
    -- P is an orthogonal projector (idempotent + self-adjoint)
    (_hP_idem : ∀ x : E d, P (P x) = P x)
    (_hP_self_adj : ∀ x y : E d, @inner ℝ _ _ (P x) y = @inner ℝ _ _ x (P y))
    -- Orthogonal decomposition (follows from hP_idem + hP_self_adj)
    (hP_ortho : ∀ v : E d, ‖v‖ ^ 2 = ‖P v‖ ^ 2 + ‖v - P v‖ ^ 2)
    -- Neighborhood Ω where we work
    (Ω : Set (E d))
    (hπ_metric : ∀ x ∈ Ω, dist x (π x) = Metric.infDist x S)
    -- Quadratic growth on Ω (from `local_fiberwise_geometry`)
    (hQG : ∀ x ∈ Ω, f x - fStar f ≥ μ' / 2 * (Metric.infDist x S) ^ 2) :
    -- Conclusion: ∃ constants C_coer, C_Ψ depending only on a = √(μ'η)
    ∃ (C_coer C_Ψ : ℝ), 0 < C_coer ∧ 0 < C_Ψ ∧
      ∀ (x₁ : E d) (n : ℕ),
        let s := nesterovSeq f η ρ x₁ n
        let Ln := lyapunov P μ' π f η ρ x₁ n
        s.x ∈ Ω →
        s.lookahead η ∈ Ω →
        -- (1) Velocity and error control
        ‖s.v‖ ^ 2 + μ' * ‖normalDisp π f η ρ x₁ n‖ ^ 2 ≤ C_coer * Ln ∧
        -- (2) Ψ control
        psi f μ' S s.x ≤ C_Ψ * Ln := by
  -- Set a = √(μ'η) and prove 0 ≤ a < 1
  set a := Real.sqrt (μ' * η) with ha_def
  have ha_nn : (0 : ℝ) ≤ a := Real.sqrt_nonneg _
  have ha_lt1 : a < 1 := by
    calc a < Real.sqrt 1 :=
          Real.sqrt_lt_sqrt (le_of_lt (mul_pos hμ' hη_pos)) hμη_lt1
      _ = 1 := Real.sqrt_one
  have h1a : (0 : ℝ) < 1 - a := by linarith
  have h1a_sq : (0 : ℝ) < (1 - a) ^ 2 := pow_pos h1a 2
  -- C_coer = 60/(1-a)², C_Ψ = 2
  refine ⟨60 / (1 - a) ^ 2, 2, div_pos (by norm_num) h1a_sq, two_pos, ?_⟩
  intro x₁ n s Ln hx hx'
  constructor
  · -- (1) ‖v_n‖² + μ'·‖e_n‖² ≤ C_coer · L_n
    -- Abbreviations
    set EE := ‖normalDisp π f η ρ x₁ n‖ with hE_def
    set U := ‖auxVar P μ' π f η ρ x₁ n‖ with hU_def
    set T := ‖P s.v‖ with hT_def
    set A := ‖s.v - P s.v‖ with hA_def
    set D := Metric.infDist s.x S with hD_def
    -- Non-negativity
    have hE_nn : 0 ≤ EE := norm_nonneg _
    have hU_nn : 0 ≤ U := norm_nonneg _
    have hT_nn : 0 ≤ T := norm_nonneg _
    have hA_nn : 0 ≤ A := norm_nonneg _
    have hD_nn : 0 ≤ D := Metric.infDist_nonneg
    have hV_nn : 0 ≤ ‖s.v‖ := norm_nonneg _
    -- Lyapunov setup
    have hlam_pos : 0 < (1 + a) ^ 2 / (2 * (1 - a)) :=
      div_pos (by positivity) (by linarith)
    have hgap_nn : 0 ≤ f s.x - fStar f := by
      linarith [hQG s.x hx,
        mul_nonneg (div_nonneg (le_of_lt hμ') two_pos.le)
          (sq_nonneg (Metric.infDist s.x S))]
    -- Lyapunov bounds
    have hgap_le : f s.x - fStar f ≤ Ln :=
      lyapunov_gap_bound (f s.x - fStar f) (U ^ 2) ((1 + a) ^ 2 / (2 * (1 - a)))
        (T ^ 2) Ln hgap_nn (sq_nonneg _) hlam_pos (sq_nonneg _) rfl
    have hu_le : U ^ 2 ≤ 2 * Ln :=
      lyapunov_u_bound (f s.x - fStar f) (U ^ 2) ((1 + a) ^ 2 / (2 * (1 - a)))
        (T ^ 2) Ln hgap_nn (sq_nonneg _) hlam_pos (sq_nonneg _) rfl
    have hLn_nn : 0 ≤ Ln := by linarith [hu_le, sq_nonneg U]
    have hPv_le : T ^ 2 ≤ 2 * Ln := by
      have hlam_ge : (1 : ℝ) / 2 ≤ (1 + a) ^ 2 / (2 * (1 - a)) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by linarith : (0 : ℝ) < 2 * (1 - a))]
        nlinarith [sq_nonneg a]
      have hPv_bound := lyapunov_Pv_bound (f s.x - fStar f) (U ^ 2)
        ((1 + a) ^ 2 / (2 * (1 - a))) (T ^ 2) Ln hgap_nn (sq_nonneg _) hlam_pos (sq_nonneg _) rfl
      calc T ^ 2 ≤ Ln / ((1 + a) ^ 2 / (2 * (1 - a))) := hPv_bound
        _ ≤ Ln / (1 / 2) := by
            apply div_le_div_of_nonneg_left hLn_nn (by norm_num : (0 : ℝ) < 1 / 2) hlam_ge
        _ = 2 * Ln := by ring
    -- QG at x_n: μ'·D² ≤ 2Ln
    have hD_sq : μ' * D ^ 2 ≤ 2 * Ln := by nlinarith [hQG s.x hx]
    -- A ≤ U + √μ'·E  (from u = P⊥v + √μ'·e)
    have hperp : A ≤ U + Real.sqrt μ' * EE := by
      have h := perp_v_bound_from_u (auxVar P μ' π f η ρ x₁ n)
        (s.v - P s.v) (normalDisp π f η ρ x₁ n) (Real.sqrt μ') rfl
      rwa [abs_of_nonneg (Real.sqrt_nonneg μ')] at h
    -- E ≤ D + √η·‖v‖  (triangle inequality)
    have hE_tri : EE ≤ D + Real.sqrt η * ‖s.v‖ := by
      have h_eq : EE = Metric.infDist (s.lookahead η) S := by
        change ‖s.lookahead η - π (s.lookahead η)‖ = _
        rw [← dist_eq_norm, hπ_metric (s.lookahead η) hx']
      have h_le : Metric.infDist (s.lookahead η) S ≤ ‖s.lookahead η - π s.x‖ := by
        rw [← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem (hπ_in_S s.x)
      have h_tri : ‖s.lookahead η - π s.x‖ ≤ D + Real.sqrt η * ‖s.v‖ := by
        change ‖(s.x + Real.sqrt η • s.v) - π s.x‖ ≤ _
        calc ‖(s.x + Real.sqrt η • s.v) - π s.x‖
            = ‖(s.x - π s.x) + Real.sqrt η • s.v‖ := by congr 1; abel
          _ ≤ ‖s.x - π s.x‖ + ‖Real.sqrt η • s.v‖ := norm_add_le _ _
          _ = ‖s.x - π s.x‖ + Real.sqrt η * ‖s.v‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg η)]
          _ = dist s.x (π s.x) + Real.sqrt η * ‖s.v‖ := by rw [dist_eq_norm]
          _ = D + Real.sqrt η * ‖s.v‖ := by rw [hD_def, hπ_metric s.x hx]
      linarith
    -- ‖v‖ ≤ A + T  (triangle)
    have hV_ub : ‖s.v‖ ≤ A + T := by
      have := norm_add_le (s.v - P s.v) (P s.v)
      simp only [sub_add_cancel] at this; exact this
    -- ‖v‖² = T² + A²  (orthogonal decomposition)
    have hv_ortho : ‖s.v‖ ^ 2 = T ^ 2 + A ^ 2 := hP_ortho s.v
    -- √μ' · √η = a
    have hsqrt_mul : Real.sqrt μ' * Real.sqrt η = a := by
      rw [ha_def, ← Real.sqrt_mul (le_of_lt hμ')]
    have hsq_mu : (Real.sqrt μ') ^ 2 = μ' := Real.sq_sqrt (le_of_lt hμ')
    have hsq_eta : (Real.sqrt η) ^ 2 = η := Real.sq_sqrt (le_of_lt hη_pos)
    -- Apply the core arithmetic lemma
    have hcore := coercivity_core_bound T A U EE D ‖s.v‖ (Real.sqrt μ') (Real.sqrt η) a μ' Ln
      ha_nn ha_lt1 hμ' (Real.sqrt_nonneg μ') (Real.sqrt_nonneg η)
      hsq_mu hsqrt_mul hE_nn hU_nn hT_nn hA_nn hD_nn hV_nn
      hPv_le hu_le hD_sq hv_ortho hperp hE_tri hV_ub
    -- Convert: goal is ‖v‖²+μ'E² ≤ 60/(1-a)²·Ln, i.e., (1-a)²(‖v‖²+μ'E²) ≤ 60Ln
    rw [div_mul_eq_mul_div, le_div_iff₀ h1a_sq]
    linarith [hcore]
  · -- (2) Ψ(x_n) ≤ 2 · L_n
    have hqg := hQG s.x hx
    have hgap_nn : 0 ≤ f s.x - fStar f := by
      have := mul_nonneg (div_nonneg (le_of_lt hμ') two_pos.le)
        (sq_nonneg (Metric.infDist s.x S))
      linarith
    have hlam_pos : 0 < (1 + a) ^ 2 / (2 * (1 - a)) :=
      div_pos (by positivity) (by linarith)
    have hpsi_le : psi f μ' S s.x ≤ 2 * (f s.x - fStar f) := by
      simp only [psi]; linarith
    have hgap_le_Ln : f s.x - fStar f ≤ Ln :=
      lyapunov_gap_bound (f s.x - fStar f) (‖auxVar P μ' π f η ρ x₁ n‖ ^ 2)
        ((1 + a) ^ 2 / (2 * (1 - a)))
        (‖P s.v‖ ^ 2) Ln
        hgap_nn (sq_nonneg _) hlam_pos (sq_nonneg _) rfl
    linarith

end PLAcceleratedNesterovLean
