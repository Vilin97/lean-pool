/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import LeanPool.PLAcceleratedNesterovLean.MorseBott.TubularProjection
import LeanPool.PLAcceleratedNesterovLean.Core.NesterovSeqGen
import LeanPool.PLAcceleratedNesterovLean.Convergence.Bootstrap.Step1
import LeanPool.PLAcceleratedNesterovLean.Convergence.Bootstrap.Step2

/-!
# Bootstrap via Total Displacement Control

Starting from a sufficiently small neighborhood of m⋆ with zero initial velocity,
all iterates remain in the controlled region Ω and the Lyapunov function
decays geometrically.
-/

noncomputable section

namespace PLAcceleratedNesterovLean

open scoped Topology NNReal
open Manifold

/-- **Bootstrap via total displacement control.**

There exists α > 0 such that for Ubar_{m⋆} = B(m⋆, α) ∩ U and every start point in
Ubar_{m⋆} with zero initial velocity:
  (1) x_n, x'_n ∈ Ω for every Lean index n
  (2) All iterates remain in U
  (3) L_n ≤ (1 - (1-θ)·a)^n · L_0

The budget-split parameter θ ∈ (0,1) is inherited from the contraction hypothesis.
-/
private abbrev bootstrapTotalDisplacementProof
    {d : ℕ} (_hd : 0 < d)
    -- The objective function
    (f : E d → ℝ)
    -- Parameters
    (L : ℝ≥0) (_hL : 0 < (L : ℝ))
    (μ' : ℝ) (hμ' : 0 < μ')
    (θ : ℝ) (hθ_pos : 0 < θ) (hθ_lt1 : θ < 1)
    (η : ℝ) (_hη : η = 1 / (L : ℝ)) (hη_pos : 0 < η)
    (hμη_lt1 : μ' * η < 1)
    (ρ : ℝ) (_hρ : ρ = (1 - Real.sqrt (μ' * η)) / (1 + Real.sqrt (μ' * η)))
    -- S = argmin set
    (S : Set (E d))
    (hM_argmin : S = argminSet f)
    -- Tubular neighborhood U
    (U : Set (E d))
    (_hTub : IsTubularNeighborhoodOfSubmanifold S U)
    -- Nearest-point projection
    (π : E d → E d)
    (_hπ_in_S : ∀ x, π x ∈ S)
    (_hπ_proj : ∀ x ∈ S, π x = x)
    (hπ_metric : ∀ x ∈ U, dist x (π x) = Metric.infDist x S)
    -- Tangent projector P
    (P : E d →L[ℝ] E d)
    -- Neighborhoods from `lyapunov_contraction`: Ω ⊂⊂ Ω⁺ ⊂⊂ U₊ ⊂ U
    (Ω : Set (E d)) (hΩ_open : IsOpen Ω) (hΩ_sub_U : Ω ⊆ U)
    -- R from `lyapunov_contraction`
    (R : ℝ) (hR : 0 < R)
    -- Base point
    (m_star : E d) (hm_star : m_star ∈ S) (hm_star_Ω : m_star ∈ Ω)
    -- Ψ continuity and vanishing at m⋆
    (hΨ_cont : ContinuousAt (psi f μ' S) m_star)
    (hΨ_zero : psi f μ' S m_star = 0)
    -- Quadratic growth (from `local_fiberwise_geometry`)
    (_hQG : ∀ x ∈ Ω, f x - fStar f ≥ μ' / 2 * (Metric.infDist x S) ^ 2)
    -- Lyapunov contraction (from `lyapunov_contraction`): whenever in Ω with L_n ≤ R²
    (hcontract : ∀ (x₁ : E d) (n : ℕ),
      let s := nesterovSeq f η ρ x₁ n
      let Ln := lyapunov P μ' π f η ρ x₁ n
      let Ln' := lyapunov P μ' π f η ρ x₁ (n + 1)
      let a := Real.sqrt (μ' * η)
      s.x ∈ Ω → s.lookahead η ∈ Ω → Ln ≤ R ^ 2 →
      Ln' ≤ (1 - (1 - θ) * a) * Ln)
    -- Motion bound on h_n (from `motion_bounds_curvature_error`)
    (C_h : ℝ) (hC_h : 0 < C_h)
    (hstep_bound : ∀ (x₁ : E d) (n : ℕ),
      let s := nesterovSeq f η ρ x₁ n
      let Ln := lyapunov P μ' π f η ρ x₁ n
      s.x ∈ Ω → s.lookahead η ∈ Ω → Ln ≤ R ^ 2 →
      ‖nesterovH f η ρ x₁ n‖ ≤ C_h * Real.sqrt η * Real.sqrt Ln)
    -- Motion bound on velocity (from `motion_bounds_curvature_error`)
    (C_mov : ℝ) (hC_mov : 0 < C_mov)
    (hvel_bound : ∀ (x₁ : E d) (n : ℕ),
      let s := nesterovSeq f η ρ x₁ n
      let s' := nesterovSeq f η ρ x₁ (n + 1)
      let Ln := lyapunov P μ' π f η ρ x₁ n
      s.x ∈ Ω → s.lookahead η ∈ Ω → Ln ≤ R ^ 2 →
      ‖Real.sqrt η • s'.v‖ ≤ C_mov * Real.sqrt Ln) :
    -- Conclusion: ∃ α > 0 with the bootstrap property
    ∃ (α : ℝ), 0 < α ∧
      ∀ x₁ ∈ Metric.ball m_star α ∩ U,
        -- (1) All iterates stay in Ω
        (∀ n : ℕ,
          (nesterovSeq f η ρ x₁ n).x ∈ Ω ∧
          (nesterovSeq f η ρ x₁ n).lookahead η ∈ Ω) ∧
        -- (2) All iterates remain in U
        (∀ n : ℕ, (nesterovSeq f η ρ x₁ n).x ∈ U) ∧
        -- (3) Geometric decay of Lyapunov function
        (∀ n : ℕ,
          let a := Real.sqrt (μ' * η)
          lyapunov P μ' π f η ρ x₁ (n + 1) ≤
            (1 - (1 - θ) * a) ^ (n + 1) * lyapunov P μ' π f η ρ x₁ 0) := by
  -- ── Contraction rate and auxiliary constants ────────────────────────────
  set a := Real.sqrt (μ' * η) with ha_def
  set c := 1 - (1 - θ) * a with hc_def
  have hμη_pos : 0 < μ' * η := mul_pos hμ' hη_pos
  have ha_pos : 0 < a := Real.sqrt_pos_of_pos hμη_pos
  have ha_lt1 : a < 1 := by
    calc a = Real.sqrt (μ' * η) := rfl
      _ < Real.sqrt 1 := Real.sqrt_lt_sqrt (le_of_lt hμη_pos) (by linarith)
      _ = 1 := Real.sqrt_one
  have hc_pos : (0 : ℝ) < c := by simp only [c]; nlinarith [mul_pos (sub_pos.mpr hθ_lt1) ha_pos]
  have hc_lt1 : c < 1 := by simp only [c]; nlinarith [mul_pos (sub_pos.mpr hθ_lt1) ha_pos]
  have hc_nonneg : (0 : ℝ) ≤ c := le_of_lt hc_pos
  have hc_le_one : c ≤ 1 := le_of_lt hc_lt1
  have hsqrt_c_lt1 : Real.sqrt c < 1 := by
    calc Real.sqrt c < Real.sqrt 1 := Real.sqrt_lt_sqrt hc_nonneg (by linarith)
      _ = 1 := Real.sqrt_one
  have h1_sub_sqrt_c_pos : (0 : ℝ) < 1 - Real.sqrt c := by linarith
  -- ── Step 1: Get r from Ω being open at m⋆ ──────────────────────────────
  obtain ⟨r, hr_pos, hball_Ω⟩ := Metric.isOpen_iff.mp hΩ_open m_star hm_star_Ω
  -- ── Step 2: Displacement bound constant ─────────────────────────────────
  -- K = C_h·√η/(1-√c) + C_mov bounds total displacement per unit √L₀.
  -- We need K·√(L₀) < r/2 so that both x' and x iterates stay in ball(m⋆,r).
  set K := C_h * Real.sqrt η / (1 - Real.sqrt c) + C_mov with hK_def
  have hK_pos : (0 : ℝ) < K := by positivity
  -- ── Step 3: Choose T so that Ψ(x₁) < T² with T ≤ R and K·T < r/2 ─────
  set T := min R (r / (4 * K)) with hT_def
  have hT_pos : (0 : ℝ) < T := lt_min hR (by positivity)
  -- ── Step 4: Get α₁ so that Ψ(x) < T² in B(m⋆, α₁) ────────────────────
  obtain ⟨α₁, hα₁_pos, hα₁_small⟩ := exists_alpha_psi_small m_star (psi f μ' S)
    hΨ_cont hΨ_zero T hT_pos
  -- ── Step 5: Set α = min(α₁, r/4) ───────────────────────────────────────
  set α := min α₁ (r / 4) with hα_def
  refine ⟨α, lt_min hα₁_pos (by linarith), fun x₁ hx₁ => ?_⟩
  -- ── Base‑case setup ─────────────────────────────────────────────────────
  have hx₁_ball : x₁ ∈ Metric.ball m_star α₁ :=
    Metric.ball_subset_ball (min_le_left α₁ (r / 4)) hx₁.1
  have hx₁_dist : dist x₁ m_star < r / 4 :=
    lt_of_lt_of_le (Metric.mem_ball.mp hx₁.1) (min_le_right α₁ (r / 4))
  have hx₁_Ω : x₁ ∈ Ω := by
    apply hball_Ω; exact Metric.mem_ball.mpr (by linarith)
  have hx₁_U : x₁ ∈ U := hx₁.2
  -- Ψ(x₁) < T²
  have hΨ_small : psi f μ' S x₁ < T ^ 2 :=
    hα₁_small x₁ (Metric.mem_ball.mp hx₁_ball)
  set L := fun n => lyapunov P μ' π f η ρ x₁ n with hL_def
  -- L 0 ≤ Ψ(x₁) (when v₁ = 0, the kinetic term vanishes)
  have hL0_le_Ψ : L 0 ≤ psi f μ' S x₁ := by
    change lyapunov P μ' π f η ρ x₁ 0 ≤ psi f μ' S x₁
    simp only [lyapunov, nesterovSeq, auxVar, normalDisp, NesterovState.lookahead,
      map_zero, smul_zero, sub_self, zero_add, add_zero, norm_zero, psi]
    have hπ_dist : dist x₁ (π x₁) = Metric.infDist x₁ S :=
      hπ_metric x₁ (hΩ_sub_U hx₁_Ω)
    rw [dist_eq_norm] at hπ_dist
    rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg μ')]
    rw [mul_pow, Real.sq_sqrt (le_of_lt hμ'), hπ_dist]
    linarith [sq_nonneg ((1 + Real.sqrt (μ' * η)) ^ 2 / (2 * (1 - Real.sqrt (μ' * η))))]
  -- L 0 ≤ T² ≤ R²
  have hL0_le_T2 : L 0 ≤ T ^ 2 := le_of_lt (lt_of_le_of_lt hL0_le_Ψ hΨ_small)
  have hT_le_R : T ≤ R := min_le_left R _
  have hL0_bound : L 0 ≤ R ^ 2 := le_trans hL0_le_T2 (by nlinarith)
  -- L 0 ≥ 0
  have hL0_nonneg : (0 : ℝ) ≤ L 0 := by
    have hmin : ∀ y, f m_star ≤ f y := by
      have : m_star ∈ argminSet f := by rw [← hM_argmin]; exact hm_star
      exact this
    have hbdd : BddBelow (Set.range f) :=
      ⟨f m_star, by rintro _ ⟨x, rfl⟩; exact hmin x⟩
    have h1 : 0 ≤ f x₁ - fStar f := sub_nonneg.mpr (ciInf_le hbdd x₁)
    change 0 ≤ lyapunov P μ' π f η ρ x₁ 0
    simp only [lyapunov, nesterovSeq, auxVar, normalDisp, NesterovState.lookahead,
      map_zero, smul_zero, sub_self, zero_add, add_zero, norm_zero]
    linarith [sq_nonneg ‖Real.sqrt μ' • (x₁ - π x₁)‖]
  -- Key bound: √(L 0) ≤ T
  have hsqrt_L0_le_T : Real.sqrt (L 0) ≤ T := by
    calc Real.sqrt (L 0) ≤ Real.sqrt (T ^ 2) := Real.sqrt_le_sqrt hL0_le_T2
      _ = T := Real.sqrt_sq (le_of_lt hT_pos)
  -- Key bound: K · √(L 0) ≤ r / 4  (since K·T ≤ K·r/(4K) = r/4)
  have hKL0 : K * Real.sqrt (L 0) ≤ r / 4 := by
    calc K * Real.sqrt (L 0)
        ≤ K * T := by apply mul_le_mul_of_nonneg_left hsqrt_L0_le_T (le_of_lt hK_pos)
      _ ≤ K * (r / (4 * K)) := by
          apply mul_le_mul_of_nonneg_left (min_le_right R _) (le_of_lt hK_pos)
      _ = r / 4 := by field_simp
  -- Displacement component: C_h·√η·√(L 0)/(1-√c) ≤ r/4
  have hdisp_bound : C_h * Real.sqrt η * Real.sqrt (L 0) / (1 - Real.sqrt c) ≤ r / 4 := by
    have : C_h * Real.sqrt η / (1 - Real.sqrt c) ≤ K :=
      le_add_of_nonneg_right (le_of_lt hC_mov)
    calc C_h * Real.sqrt η * Real.sqrt (L 0) / (1 - Real.sqrt c)
        = C_h * Real.sqrt η / (1 - Real.sqrt c) * Real.sqrt (L 0) := by ring
      _ ≤ K * Real.sqrt (L 0) := by
          apply mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)
      _ ≤ r / 4 := hKL0
  -- Velocity component: C_mov · √(L 0) ≤ r/4
  have hvel_comp : C_mov * Real.sqrt (L 0) ≤ r / 4 := by
    have : C_mov ≤ K := le_add_of_nonneg_left (by positivity)
    calc C_mov * Real.sqrt (L 0) ≤ K * Real.sqrt (L 0) :=
          mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)
      _ ≤ r / 4 := hKL0
  -- ── Main induction ─────────────────────────────────────────────────────
  -- Invariant: Ω-membership + Lyapunov decay + lookahead displacement bound
  -- D(n) := dist(x'_n, m⋆)  ≤  dist(x₁,m⋆) + C_h·√η·√(L 0)·Σ_{k<n}(√c)^k
  have hinduction : ∀ n,
      ((nesterovSeq f η ρ x₁ n).x ∈ Ω ∧
       (nesterovSeq f η ρ x₁ n).lookahead η ∈ Ω) ∧
      L n ≤ c ^ n * L 0 ∧
      dist ((nesterovSeq f η ρ x₁ n).lookahead η) m_star ≤
        dist x₁ m_star + C_h * Real.sqrt η * Real.sqrt (L 0) *
          (Finset.range n).sum (fun k => Real.sqrt c ^ k) := by
    intro n
    induction n with
    | zero =>
      refine ⟨⟨hx₁_Ω, ?_⟩, by simp only [pow_zero, one_mul, le_refl], ?_⟩
      · -- x'₀ ∈ Ω (v₀ = 0 so x'₀ = x₁)
        simp only [NesterovState.lookahead, nesterovSeq, smul_zero, add_zero]; exact hx₁_Ω
      · -- displacement base case
        simp only [NesterovState.lookahead, nesterovSeq,
          smul_zero, add_zero, Finset.range_zero,
          Finset.sum_empty, mul_zero, le_refl]
    | succ n ih =>
      obtain ⟨⟨hxn_Ω, hxn'_Ω⟩, hLn, hDn⟩ := ih
      -- L n ≤ R² (from c^n ≤ 1 and L 0 ≤ R²)
      have hLn_R : L n ≤ R ^ 2 := by
        have hcn : c ^ n ≤ 1 := pow_le_one₀ hc_nonneg hc_le_one
        have hcnL0 : c ^ n * L 0 ≤ L 0 := mul_le_of_le_one_left hL0_nonneg hcn
        linarith
      -- Motion bounds
      have hh_bound : ‖nesterovH f η ρ x₁ n‖ ≤ C_h * Real.sqrt η * Real.sqrt (L n) :=
        hstep_bound x₁ n hxn_Ω hxn'_Ω hLn_R
      have hv_bound : ‖Real.sqrt η • (nesterovSeq f η ρ x₁ (n + 1)).v‖ ≤
          C_mov * Real.sqrt (L n) :=
        hvel_bound x₁ n hxn_Ω hxn'_Ω hLn_R
      -- √(c^m) = (√c)^m for any m
      have sqrt_pow_c : ∀ m : ℕ, Real.sqrt (c ^ m) = Real.sqrt c ^ m := by
        intro m; induction m with
        | zero => simp only [pow_zero, Real.sqrt_one]
        | succ k ihk =>
          rw [pow_succ, Real.sqrt_mul (pow_nonneg hc_nonneg k), ihk, pow_succ]
      -- √(L n) ≤ (√c)^n · √(L 0)
      have hsqrt_Ln : Real.sqrt (L n) ≤ Real.sqrt c ^ n * Real.sqrt (L 0) := by
        calc Real.sqrt (L n) ≤ Real.sqrt (c ^ n * L 0) :=
              Real.sqrt_le_sqrt hLn
          _ = Real.sqrt (c ^ n) * Real.sqrt (L 0) :=
              Real.sqrt_mul (pow_nonneg hc_nonneg n) (L 0)
          _ = Real.sqrt c ^ n * Real.sqrt (L 0) := by rw [sqrt_pow_c]
      -- ‖h_n‖ ≤ C_h·√η·√(L 0)·(√c)^n
      have hh_geom : ‖nesterovH f η ρ x₁ n‖ ≤
          C_h * Real.sqrt η * Real.sqrt (L 0) * Real.sqrt c ^ n := by
        calc ‖nesterovH f η ρ x₁ n‖
            ≤ C_h * Real.sqrt η * Real.sqrt (L n) := hh_bound
          _ ≤ C_h * Real.sqrt η * (Real.sqrt c ^ n * Real.sqrt (L 0)) := by
              apply mul_le_mul_of_nonneg_left hsqrt_Ln
              apply mul_nonneg (le_of_lt hC_h) (Real.sqrt_nonneg _)
          _ = C_h * Real.sqrt η * Real.sqrt (L 0) * Real.sqrt c ^ n := by ring
      -- ── Displacement bound for x'_{n+1} ────────────────────────────────
      -- x'_{n+1} = x'_n + h_n  (by definition of nesterovH)
      -- dist(x'_{n+1}, m⋆) ≤ dist(x'_n, m⋆) + ‖h_n‖
      have hDn1 : dist ((nesterovSeq f η ρ x₁ (n + 1)).lookahead η) m_star ≤
          dist x₁ m_star + C_h * Real.sqrt η * Real.sqrt (L 0) *
            (Finset.range (n + 1)).sum (fun k => Real.sqrt c ^ k) := by
        -- h_n = x'_{n+1} - x'_n
        have hH_def : nesterovH f η ρ x₁ n =
          (nesterovSeq f η ρ x₁ (n + 1)).lookahead η -
          (nesterovSeq f η ρ x₁ n).lookahead η := rfl
        -- So x'_{n+1} = x'_n + h_n
        have hla_step : (nesterovSeq f η ρ x₁ (n + 1)).lookahead η =
          (nesterovSeq f η ρ x₁ n).lookahead η + nesterovH f η ρ x₁ n := by
          rw [hH_def]; abel
        calc dist ((nesterovSeq f η ρ x₁ (n + 1)).lookahead η) m_star
            = dist ((nesterovSeq f η ρ x₁ n).lookahead η +
                nesterovH f η ρ x₁ n) m_star := by rw [hla_step]
          _ ≤ dist ((nesterovSeq f η ρ x₁ n).lookahead η) m_star +
                ‖nesterovH f η ρ x₁ n‖ := by
              rw [dist_eq_norm, dist_eq_norm]
              calc ‖(nesterovSeq f η ρ x₁ n).lookahead η +
                      nesterovH f η ρ x₁ n - m_star‖
                  = ‖((nesterovSeq f η ρ x₁ n).lookahead η - m_star) +
                      nesterovH f η ρ x₁ n‖ := by congr 1; abel
                _ ≤ ‖(nesterovSeq f η ρ x₁ n).lookahead η - m_star‖ +
                      ‖nesterovH f η ρ x₁ n‖ := norm_add_le _ _
          _ ≤ (dist x₁ m_star + C_h * Real.sqrt η * Real.sqrt (L 0) *
                (Finset.range n).sum (fun k => Real.sqrt c ^ k)) +
              C_h * Real.sqrt η * Real.sqrt (L 0) * Real.sqrt c ^ n := by
              linarith [hDn, hh_geom]
          _ = dist x₁ m_star + C_h * Real.sqrt η * Real.sqrt (L 0) *
                (Finset.range (n + 1)).sum (fun k => Real.sqrt c ^ k) := by
              rw [Finset.sum_range_succ]; ring
      -- Tighter displacement upper bound: dist(x'_{n+1}, m⋆) ≤ r/4 + r/4 = r/2
      have hDn1_le_half : dist ((nesterovSeq f η ρ x₁ (n + 1)).lookahead η) m_star ≤
          r / 2 := by
        have hsum_bound : C_h * Real.sqrt η * Real.sqrt (L 0) *
            (Finset.range (n + 1)).sum (fun k => Real.sqrt c ^ k) ≤ r / 4 := by
          have hle := partial_geom_series_bound (Real.sqrt c)
            (Real.sqrt_nonneg c) hsqrt_c_lt1 (n + 1)
          calc C_h * Real.sqrt η * Real.sqrt (L 0) *
                (Finset.range (n + 1)).sum (fun k => Real.sqrt c ^ k)
              ≤ C_h * Real.sqrt η * Real.sqrt (L 0) * (1 / (1 - Real.sqrt c)) := by
                apply mul_le_mul_of_nonneg_left hle
                apply mul_nonneg (mul_nonneg (le_of_lt hC_h) (Real.sqrt_nonneg _))
                  (Real.sqrt_nonneg _)
            _ = C_h * Real.sqrt η * Real.sqrt (L 0) / (1 - Real.sqrt c) := by ring
            _ ≤ r / 4 := hdisp_bound
        linarith [hDn1, hx₁_dist]
      have hDn1_lt_r : dist ((nesterovSeq f η ρ x₁ (n + 1)).lookahead η) m_star < r := by
        linarith
      -- ── Velocity bound for x_{n+1} ─────────────────────────────────────
      -- C_mov · √(L n) ≤ C_mov · √(L 0) ≤ r/4
      have hvel_Ln : C_mov * Real.sqrt (L n) ≤ r / 4 := by
        have hLn_le_L0 : L n ≤ L 0 := by
          have := pow_le_one₀ hc_nonneg hc_le_one (n := n)
          have := mul_le_of_le_one_left hL0_nonneg this
          linarith
        calc C_mov * Real.sqrt (L n)
            ≤ C_mov * Real.sqrt (L 0) := by
              apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hLn_le_L0) (le_of_lt hC_mov)
          _ ≤ r / 4 := hvel_comp
      -- ── x_{n+1} ∈ Ω ──
      -- dist(x'_{n+1}, m⋆) ≤ r/2, dist(x_{n+1}, m⋆) ≤ r/2 + r/4 = 3r/4 < r
      have hxn1_mem : (nesterovSeq f η ρ x₁ (n + 1)).x ∈ Ω := by
        apply hball_Ω; rw [Metric.mem_ball]
        -- x = x' - √η · v, so dist(x, m⋆) ≤ dist(x', m⋆) + ‖√η · v‖
        have hx_eq : (nesterovSeq f η ρ x₁ (n + 1)).x =
            (nesterovSeq f η ρ x₁ (n + 1)).lookahead η -
            Real.sqrt η • (nesterovSeq f η ρ x₁ (n + 1)).v := by
          simp only [NesterovState.lookahead, add_sub_cancel_right]
        calc dist (nesterovSeq f η ρ x₁ (n + 1)).x m_star
            = dist ((nesterovSeq f η ρ x₁ (n + 1)).lookahead η -
                Real.sqrt η • (nesterovSeq f η ρ x₁ (n + 1)).v) m_star := by
              rw [hx_eq]
          _ ≤ dist ((nesterovSeq f η ρ x₁ (n + 1)).lookahead η) m_star +
                ‖Real.sqrt η • (nesterovSeq f η ρ x₁ (n + 1)).v‖ := by
              rw [dist_eq_norm, dist_eq_norm]
              calc ‖(nesterovSeq f η ρ x₁ (n + 1)).lookahead η -
                      Real.sqrt η • (nesterovSeq f η ρ x₁ (n + 1)).v - m_star‖
                  = ‖((nesterovSeq f η ρ x₁ (n + 1)).lookahead η - m_star) -
                      Real.sqrt η • (nesterovSeq f η ρ x₁ (n + 1)).v‖ := by
                    congr 1; abel
                _ ≤ ‖(nesterovSeq f η ρ x₁ (n + 1)).lookahead η - m_star‖ +
                      ‖Real.sqrt η • (nesterovSeq f η ρ x₁ (n + 1)).v‖ :=
                    norm_sub_le _ _
          _ ≤ dist ((nesterovSeq f η ρ x₁ (n + 1)).lookahead η) m_star +
                C_mov * Real.sqrt (L n) := by linarith [hv_bound]
          _ ≤ r / 2 + r / 4 := by linarith [hDn1_le_half, hvel_Ln]
          _ < r := by linarith
      -- ── x'_{n+1} ∈ Ω ───────────────────────────────────────────────────
      have hxn1'_mem : (nesterovSeq f η ρ x₁ (n + 1)).lookahead η ∈ Ω := by
        apply hball_Ω; exact Metric.mem_ball.mpr hDn1_lt_r
      -- ── Assemble ────────────────────────────────────────────────────────
      refine ⟨⟨hxn1_mem, hxn1'_mem⟩, ?_, hDn1⟩
      -- Lyapunov decay: L(n+1) ≤ c^{n+1} · L 0
      calc L (n + 1) ≤ c * L n := hcontract x₁ n hxn_Ω hxn'_Ω hLn_R
        _ ≤ c * (c ^ n * L 0) := by
            apply mul_le_mul_of_nonneg_left hLn hc_nonneg
        _ = c ^ (n + 1) * L 0 := by ring
  refine ⟨fun n => (hinduction n).1, fun n => ?_, fun n => ?_⟩
  · -- (2) All iterates remain in U
    exact hΩ_sub_U (hinduction n).1.1
  · -- (3) Geometric decay
    exact (hinduction (n + 1)).2.1


-- Bootstrap argument requires additional heartbeats for the proof term

/-- **Generalized bootstrap via total displacement control.**

For any state s₀ near m⋆ with sufficiently small Lyapunov value,
all iterates of `nesterovSeqGen` stay in the controlled region Ω and the
Lyapunov function decays geometrically.

Generalization of `bootstrap_total_displacement` supporting nonzero initial velocity,
which is essential for the Nesterov algorithm where velocity carries across
iterations.
-/
private abbrev bootstrapTotalDisplacementGenProof
    {d : ℕ}
    (f : E d → ℝ)
    (μ' : ℝ) (hμ' : 0 < μ')
    (θ : ℝ) (hθ_pos : 0 < θ) (hθ_lt1 : θ < 1)
    (η : ℝ) (hη_pos : 0 < η)
    (hμη_lt1 : μ' * η < 1)
    (ρ : ℝ)
    (S : Set (E d))
    (hM_argmin : S = argminSet f)
    (π : E d → E d)
    (P : E d →L[ℝ] E d)
    (Ω : Set (E d)) (hΩ_open : IsOpen Ω)
    (R : ℝ) (hR : 0 < R)
    (m_star : E d) (hm_star : m_star ∈ S) (hm_star_Ω : m_star ∈ Ω)
    -- Contraction (from lyapunov_contraction_gen)
    (hcontract : ∀ (s₀ : NesterovState d) (n : ℕ),
      let s := nesterovSeqGen f η ρ s₀ n
      s.x ∈ Ω → s.lookahead η ∈ Ω →
      lyapunovOfState P μ' π f η s ≤ R ^ 2 →
      lyapunovOfState P μ' π f η (nesterovSeqGen f η ρ s₀ (n + 1)) ≤
        (1 - (1 - θ) * Real.sqrt (μ' * η)) *
        lyapunovOfState P μ' π f η s)
    -- Step displacement bound
    (C_h : ℝ) (hC_h : 0 < C_h)
    (hstep_bound : ∀ (s₀ : NesterovState d) (n : ℕ),
      let s := nesterovSeqGen f η ρ s₀ n
      s.x ∈ Ω → s.lookahead η ∈ Ω →
      lyapunovOfState P μ' π f η s ≤ R ^ 2 →
      ‖stepDispOfState f η ρ s‖ ≤
        C_h * Real.sqrt η *
        Real.sqrt (lyapunovOfState P μ' π f η s))
    -- Velocity bound
    (C_mov : ℝ) (hC_mov : 0 < C_mov)
    (hvel_bound : ∀ (s₀ : NesterovState d) (n : ℕ),
      let s := nesterovSeqGen f η ρ s₀ n
      s.x ∈ Ω → s.lookahead η ∈ Ω →
      lyapunovOfState P μ' π f η s ≤ R ^ 2 →
      ‖Real.sqrt η • (nesterovSeqGen f η ρ s₀ (n + 1)).v‖ ≤
        C_mov * Real.sqrt (lyapunovOfState P μ' π f η s)) :
    ∃ (δ r_ball : ℝ), 0 < δ ∧ 0 < r_ball ∧
      Metric.ball m_star r_ball ⊆ Ω ∧
      ∀ s₀ : NesterovState d,
        s₀.x ∈ Metric.ball m_star δ →
        s₀.lookahead η ∈ Metric.ball m_star δ →
        lyapunovOfState P μ' π f η s₀ ≤ δ ^ 2 →
        -- (1) All iterates stay in Ω
        (∀ n : ℕ,
          (nesterovSeqGen f η ρ s₀ n).x ∈ Ω ∧
          (nesterovSeqGen f η ρ s₀ n).lookahead η ∈ Ω) ∧
        -- (2) Ball containment: iterates stay in ball(m_star, r_ball)
        (∀ n : ℕ,
          (nesterovSeqGen f η ρ s₀ n).x ∈ Metric.ball m_star r_ball ∧
          (nesterovSeqGen f η ρ s₀ n).lookahead η ∈ Metric.ball m_star r_ball) ∧
        -- (3) Geometric decay
        (∀ n : ℕ,
          let a := Real.sqrt (μ' * η)
          lyapunovOfState P μ' π f η (nesterovSeqGen f η ρ s₀ (n + 1)) ≤
            (1 - (1 - θ) * a) ^ (n + 1) *
            lyapunovOfState P μ' π f η s₀) := by
  -- ── Contraction rate and auxiliary constants ────────────────────────────
  set a := Real.sqrt (μ' * η) with ha_def
  set c := 1 - (1 - θ) * a with hc_def
  have hμη_pos : 0 < μ' * η := mul_pos hμ' hη_pos
  have ha_pos : 0 < a := Real.sqrt_pos_of_pos hμη_pos
  have ha_lt1 : a < 1 := by
    calc a = Real.sqrt (μ' * η) := rfl
      _ < Real.sqrt 1 := Real.sqrt_lt_sqrt (le_of_lt hμη_pos) (by linarith)
      _ = 1 := Real.sqrt_one
  have hc_pos : (0 : ℝ) < c := by simp only [c]; nlinarith [mul_pos (sub_pos.mpr hθ_lt1) ha_pos]
  have hc_lt1 : c < 1 := by simp only [c]; nlinarith [mul_pos (sub_pos.mpr hθ_lt1) ha_pos]
  have hc_nonneg : (0 : ℝ) ≤ c := le_of_lt hc_pos
  have hc_le_one : c ≤ 1 := le_of_lt hc_lt1
  have hsqrt_c_lt1 : Real.sqrt c < 1 := by
    calc Real.sqrt c < Real.sqrt 1 := Real.sqrt_lt_sqrt hc_nonneg (by linarith)
      _ = 1 := Real.sqrt_one
  have h1_sub_sqrt_c_pos : (0 : ℝ) < 1 - Real.sqrt c := by linarith
  -- ── Step 1: Get r from Ω being open at m⋆ ──────────────────────────────
  obtain ⟨r, hr_pos, hball_Ω⟩ := Metric.isOpen_iff.mp hΩ_open m_star hm_star_Ω
  -- ── Step 2: Displacement bound constant ─────────────────────────────────
  set K := C_h * Real.sqrt η / (1 - Real.sqrt c) + C_mov with hK_def
  have hK_pos : (0 : ℝ) < K := by positivity
  -- ── Step 3: Choose δ so that iterates stay within ball(m⋆, r) ⊆ Ω ──────
  set δ := min R (min (r / 4) (r / (4 * K))) with hδ_def
  have hδ_pos : (0 : ℝ) < δ := by
    apply lt_min hR; apply lt_min (by linarith) (by positivity)
  have hδ_le_R : δ ≤ R := min_le_left R _
  have hδ_le_r4 : δ ≤ r / 4 := le_trans (min_le_right R _) (min_le_left _ _)
  have hδ_le_rK : δ ≤ r / (4 * K) := le_trans (min_le_right R _) (min_le_right _ _)
  refine ⟨δ, r, hδ_pos, hr_pos, hball_Ω, fun s₀ hs₀_x hs₀_la hL₀_small => ?_⟩
  -- ── Starting state bounds ───────────────────────────────────────────────
  have hs₀_x_dist : dist s₀.x m_star < r / 4 :=
    lt_of_lt_of_le (Metric.mem_ball.mp hs₀_x) hδ_le_r4
  have hs₀_la_dist : dist (s₀.lookahead η) m_star < r / 4 :=
    lt_of_lt_of_le (Metric.mem_ball.mp hs₀_la) hδ_le_r4
  have hs₀_x_Ω : s₀.x ∈ Ω :=
    hball_Ω (Metric.mem_ball.mpr (by linarith))
  have hs₀_la_Ω : s₀.lookahead η ∈ Ω :=
    hball_Ω (Metric.mem_ball.mpr (by linarith))
  -- L₀ ≤ R²
  have hL₀_R : lyapunovOfState P μ' π f η s₀ ≤ R ^ 2 :=
    le_trans hL₀_small (by nlinarith [hδ_le_R])
  -- L₀ ≥ 0
  have hbdd : BddBelow (Set.range f) := by
    refine ⟨f m_star, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (hM_argmin ▸ hm_star : m_star ∈ argminSet f) x
  set L₀ := lyapunovOfState P μ' π f η s₀ with hL₀_def
  have hL₀_nonneg : 0 ≤ L₀ :=
    lyapunovOfState_nonneg P μ' π f η s₀ hμ' hη_pos hμη_lt1 hbdd
  -- √L₀ ≤ δ
  have hsqrt_L₀_le_δ : Real.sqrt L₀ ≤ δ := by
    calc Real.sqrt L₀ ≤ Real.sqrt (δ ^ 2) := Real.sqrt_le_sqrt hL₀_small
      _ = δ := Real.sqrt_sq (le_of_lt hδ_pos)
  -- K · √L₀ ≤ r/4
  have hKL₀ : K * Real.sqrt L₀ ≤ r / 4 := by
    calc K * Real.sqrt L₀
        ≤ K * δ := mul_le_mul_of_nonneg_left hsqrt_L₀_le_δ (le_of_lt hK_pos)
      _ ≤ K * (r / (4 * K)) := mul_le_mul_of_nonneg_left hδ_le_rK (le_of_lt hK_pos)
      _ = r / 4 := by field_simp
  -- C_h·√η·√L₀/(1-√c) ≤ r/4
  have hdisp_bound : C_h * Real.sqrt η * Real.sqrt L₀ / (1 - Real.sqrt c) ≤ r / 4 := by
    have : C_h * Real.sqrt η / (1 - Real.sqrt c) ≤ K :=
      le_add_of_nonneg_right (le_of_lt hC_mov)
    calc C_h * Real.sqrt η * Real.sqrt L₀ / (1 - Real.sqrt c)
        = C_h * Real.sqrt η / (1 - Real.sqrt c) * Real.sqrt L₀ := by ring
      _ ≤ K * Real.sqrt L₀ :=
          mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)
      _ ≤ r / 4 := hKL₀
  -- C_mov · √L₀ ≤ r/4
  have hvel_comp : C_mov * Real.sqrt L₀ ≤ r / 4 := by
    have : C_mov ≤ K := le_add_of_nonneg_left (by positivity)
    calc C_mov * Real.sqrt L₀ ≤ K * Real.sqrt L₀ :=
          mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)
      _ ≤ r / 4 := hKL₀
  -- ── Main induction ─────────────────────────────────────────────────────
  set Ln := fun n => lyapunovOfState P μ' π f η (nesterovSeqGen f η ρ s₀ n) with hLn_def
  have hinduction : ∀ n,
      ((nesterovSeqGen f η ρ s₀ n).x ∈ Ω ∧
       (nesterovSeqGen f η ρ s₀ n).lookahead η ∈ Ω) ∧
      Ln n ≤ c ^ n * L₀ ∧
      dist ((nesterovSeqGen f η ρ s₀ n).lookahead η) m_star ≤
        dist (s₀.lookahead η) m_star + C_h * Real.sqrt η * Real.sqrt L₀ *
          (Finset.range n).sum (fun k => Real.sqrt c ^ k) := by
    intro n
    induction n with
    | zero =>
      refine ⟨⟨hs₀_x_Ω, hs₀_la_Ω⟩, ?_, ?_⟩
      · -- Ln 0 ≤ c ^ 0 * L₀
        have h1 : Ln 0 = L₀ := rfl
        linarith [pow_zero c]
      · simp only [nesterovSeqGen, Finset.range_zero, Finset.sum_empty, mul_zero,
          add_zero, le_refl]
    | succ n ih =>
      obtain ⟨⟨hxn_Ω, hxn'_Ω⟩, hLn_decay, hDn⟩ := ih
      -- Ln ≤ R²
      have hLn_R : Ln n ≤ R ^ 2 := by
        have hcn : c ^ n ≤ 1 := pow_le_one₀ hc_nonneg hc_le_one
        have hcnL₀ : c ^ n * L₀ ≤ L₀ := mul_le_of_le_one_left hL₀_nonneg hcn
        linarith
      -- Motion bounds at step n
      have hh_bound : ‖stepDispOfState f η ρ (nesterovSeqGen f η ρ s₀ n)‖ ≤
          C_h * Real.sqrt η * Real.sqrt (Ln n) :=
        hstep_bound s₀ n hxn_Ω hxn'_Ω hLn_R
      have hv_bound : ‖Real.sqrt η • (nesterovSeqGen f η ρ s₀ (n + 1)).v‖ ≤
          C_mov * Real.sqrt (Ln n) :=
        hvel_bound s₀ n hxn_Ω hxn'_Ω hLn_R
      -- √(c^m) = (√c)^m
      have sqrt_pow_c : ∀ m : ℕ, Real.sqrt (c ^ m) = Real.sqrt c ^ m := by
        intro m; induction m with
        | zero => simp only [pow_zero, Real.sqrt_one]
        | succ k ihk =>
          rw [pow_succ, Real.sqrt_mul (pow_nonneg hc_nonneg k), ihk, pow_succ]
      -- √(Ln n) ≤ (√c)^n · √L₀
      have hsqrt_Ln : Real.sqrt (Ln n) ≤ Real.sqrt c ^ n * Real.sqrt L₀ := by
        calc Real.sqrt (Ln n) ≤ Real.sqrt (c ^ n * L₀) :=
              Real.sqrt_le_sqrt hLn_decay
          _ = Real.sqrt (c ^ n) * Real.sqrt L₀ :=
              Real.sqrt_mul (pow_nonneg hc_nonneg n) L₀
          _ = Real.sqrt c ^ n * Real.sqrt L₀ := by rw [sqrt_pow_c]
      -- ‖h_n‖ ≤ C_h·√η·√L₀·(√c)^n
      have hh_geom : ‖stepDispOfState f η ρ (nesterovSeqGen f η ρ s₀ n)‖ ≤
          C_h * Real.sqrt η * Real.sqrt L₀ * Real.sqrt c ^ n := by
        calc ‖stepDispOfState f η ρ (nesterovSeqGen f η ρ s₀ n)‖
            ≤ C_h * Real.sqrt η * Real.sqrt (Ln n) := hh_bound
          _ ≤ C_h * Real.sqrt η * (Real.sqrt c ^ n * Real.sqrt L₀) := by
              apply mul_le_mul_of_nonneg_left hsqrt_Ln
              apply mul_nonneg (le_of_lt hC_h) (Real.sqrt_nonneg _)
          _ = C_h * Real.sqrt η * Real.sqrt L₀ * Real.sqrt c ^ n := by ring
      -- ── Displacement bound for lookahead at n+1 ────────────────────────
      have hla_step : (nesterovSeqGen f η ρ s₀ (n + 1)).lookahead η =
          (nesterovSeqGen f η ρ s₀ n).lookahead η +
          stepDispOfState f η ρ (nesterovSeqGen f η ρ s₀ n) := by
        simp only [stepDispOfState, nesterovSeqGen]; abel
      have hDn1 : dist ((nesterovSeqGen f η ρ s₀ (n + 1)).lookahead η) m_star ≤
          dist (s₀.lookahead η) m_star + C_h * Real.sqrt η * Real.sqrt L₀ *
            (Finset.range (n + 1)).sum (fun k => Real.sqrt c ^ k) := by
        calc dist ((nesterovSeqGen f η ρ s₀ (n + 1)).lookahead η) m_star
            = dist ((nesterovSeqGen f η ρ s₀ n).lookahead η +
                stepDispOfState f η ρ (nesterovSeqGen f η ρ s₀ n)) m_star := by
              rw [hla_step]
          _ ≤ dist ((nesterovSeqGen f η ρ s₀ n).lookahead η) m_star +
                ‖stepDispOfState f η ρ (nesterovSeqGen f η ρ s₀ n)‖ := by
              rw [dist_eq_norm, dist_eq_norm]
              calc ‖(nesterovSeqGen f η ρ s₀ n).lookahead η +
                      stepDispOfState f η ρ (nesterovSeqGen f η ρ s₀ n) - m_star‖
                  = ‖((nesterovSeqGen f η ρ s₀ n).lookahead η - m_star) +
                      stepDispOfState f η ρ (nesterovSeqGen f η ρ s₀ n)‖ := by
                    congr 1; abel
                _ ≤ ‖(nesterovSeqGen f η ρ s₀ n).lookahead η - m_star‖ +
                      ‖stepDispOfState f η ρ (nesterovSeqGen f η ρ s₀ n)‖ :=
                    norm_add_le _ _
          _ ≤ (dist (s₀.lookahead η) m_star + C_h * Real.sqrt η * Real.sqrt L₀ *
                (Finset.range n).sum (fun k => Real.sqrt c ^ k)) +
              C_h * Real.sqrt η * Real.sqrt L₀ * Real.sqrt c ^ n := by
              linarith [hDn, hh_geom]
          _ = dist (s₀.lookahead η) m_star + C_h * Real.sqrt η * Real.sqrt L₀ *
                (Finset.range (n + 1)).sum (fun k => Real.sqrt c ^ k) := by
              rw [Finset.sum_range_succ]; ring
      -- dist(x'_{n+1}, m⋆) ≤ r/2
      have hDn1_le_half : dist ((nesterovSeqGen f η ρ s₀ (n + 1)).lookahead η) m_star ≤
          r / 2 := by
        have hsum_bound : C_h * Real.sqrt η * Real.sqrt L₀ *
            (Finset.range (n + 1)).sum (fun k => Real.sqrt c ^ k) ≤ r / 4 := by
          have hle := partial_geom_series_bound (Real.sqrt c)
            (Real.sqrt_nonneg c) hsqrt_c_lt1 (n + 1)
          calc C_h * Real.sqrt η * Real.sqrt L₀ *
                (Finset.range (n + 1)).sum (fun k => Real.sqrt c ^ k)
              ≤ C_h * Real.sqrt η * Real.sqrt L₀ * (1 / (1 - Real.sqrt c)) := by
                apply mul_le_mul_of_nonneg_left hle
                apply mul_nonneg (mul_nonneg (le_of_lt hC_h) (Real.sqrt_nonneg _))
                  (Real.sqrt_nonneg _)
            _ = C_h * Real.sqrt η * Real.sqrt L₀ / (1 - Real.sqrt c) := by ring
            _ ≤ r / 4 := hdisp_bound
        linarith [hDn1, hs₀_la_dist]
      have hDn1_lt_r : dist ((nesterovSeqGen f η ρ s₀ (n + 1)).lookahead η) m_star < r := by
        linarith
      -- ── Velocity bound ─────────────────────────────────────────────────
      have hvel_Ln : C_mov * Real.sqrt (Ln n) ≤ r / 4 := by
        have hLn_le_L₀ : Ln n ≤ L₀ := by
          have := pow_le_one₀ hc_nonneg hc_le_one (n := n)
          have := mul_le_of_le_one_left hL₀_nonneg this
          linarith
        calc C_mov * Real.sqrt (Ln n)
            ≤ C_mov * Real.sqrt L₀ := by
              apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hLn_le_L₀) (le_of_lt hC_mov)
          _ ≤ r / 4 := hvel_comp
      -- ── x_{n+1} ∈ Ω ───────────────────────────────────────────────────
      have hxn1_mem : (nesterovSeqGen f η ρ s₀ (n + 1)).x ∈ Ω := by
        apply hball_Ω; rw [Metric.mem_ball]
        have hx_eq : (nesterovSeqGen f η ρ s₀ (n + 1)).x =
            (nesterovSeqGen f η ρ s₀ (n + 1)).lookahead η -
            Real.sqrt η • (nesterovSeqGen f η ρ s₀ (n + 1)).v := by
          simp only [NesterovState.lookahead, add_sub_cancel_right]
        calc dist (nesterovSeqGen f η ρ s₀ (n + 1)).x m_star
            = dist ((nesterovSeqGen f η ρ s₀ (n + 1)).lookahead η -
                Real.sqrt η • (nesterovSeqGen f η ρ s₀ (n + 1)).v) m_star := by
              rw [hx_eq]
          _ ≤ dist ((nesterovSeqGen f η ρ s₀ (n + 1)).lookahead η) m_star +
                ‖Real.sqrt η • (nesterovSeqGen f η ρ s₀ (n + 1)).v‖ := by
              rw [dist_eq_norm, dist_eq_norm]
              calc ‖(nesterovSeqGen f η ρ s₀ (n + 1)).lookahead η -
                      Real.sqrt η • (nesterovSeqGen f η ρ s₀ (n + 1)).v - m_star‖
                  = ‖((nesterovSeqGen f η ρ s₀ (n + 1)).lookahead η - m_star) -
                      Real.sqrt η • (nesterovSeqGen f η ρ s₀ (n + 1)).v‖ := by
                    congr 1; abel
                _ ≤ ‖(nesterovSeqGen f η ρ s₀ (n + 1)).lookahead η - m_star‖ +
                      ‖Real.sqrt η • (nesterovSeqGen f η ρ s₀ (n + 1)).v‖ :=
                    norm_sub_le _ _
          _ ≤ dist ((nesterovSeqGen f η ρ s₀ (n + 1)).lookahead η) m_star +
                C_mov * Real.sqrt (Ln n) := by linarith [hv_bound]
          _ ≤ r / 2 + r / 4 := by linarith [hDn1_le_half, hvel_Ln]
          _ < r := by linarith
      -- ── x'_{n+1} ∈ Ω ──────────────────────────────────────────────────
      have hxn1'_mem : (nesterovSeqGen f η ρ s₀ (n + 1)).lookahead η ∈ Ω :=
        hball_Ω (Metric.mem_ball.mpr hDn1_lt_r)
      -- ── Assemble ───────────────────────────────────────────────────────
      refine ⟨⟨hxn1_mem, hxn1'_mem⟩, ?_, hDn1⟩
      -- Lyapunov decay: L_{n+1} ≤ c^{n+1} · L₀
      calc Ln (n + 1) ≤ c * Ln n := hcontract s₀ n hxn_Ω hxn'_Ω hLn_R
        _ ≤ c * (c ^ n * L₀) :=
            mul_le_mul_of_nonneg_left hLn_decay hc_nonneg
        _ = c ^ (n + 1) * L₀ := by ring
  -- Ball containment follows from the induction: dist(la, m_star) ≤ r/2 and dist(x, m_star) < r
  have hball_contain : ∀ n,
      (nesterovSeqGen f η ρ s₀ n).x ∈ Metric.ball m_star r ∧
      (nesterovSeqGen f η ρ s₀ n).lookahead η ∈ Metric.ball m_star r := by
    intro n
    obtain ⟨_, hLn_decay, hDn⟩ := hinduction n
    -- lookahead distance bound: dist(la(n), m_star) < r/2
    have hla_dist : dist ((nesterovSeqGen f η ρ s₀ n).lookahead η) m_star < r := by
      have hsum_bound : C_h * Real.sqrt η * Real.sqrt L₀ *
          (Finset.range n).sum (fun k => Real.sqrt c ^ k) ≤ r / 4 := by
        have hle := partial_geom_series_bound (Real.sqrt c)
          (Real.sqrt_nonneg c) hsqrt_c_lt1 n
        calc C_h * Real.sqrt η * Real.sqrt L₀ *
              (Finset.range n).sum (fun k => Real.sqrt c ^ k)
            ≤ C_h * Real.sqrt η * Real.sqrt L₀ * (1 / (1 - Real.sqrt c)) := by
              apply mul_le_mul_of_nonneg_left hle
              apply mul_nonneg (mul_nonneg (le_of_lt hC_h) (Real.sqrt_nonneg _))
                (Real.sqrt_nonneg _)
          _ = C_h * Real.sqrt η * Real.sqrt L₀ / (1 - Real.sqrt c) := by ring
          _ ≤ r / 4 := hdisp_bound
      linarith [hDn, hs₀_la_dist]
    refine ⟨?_, Metric.mem_ball.mpr hla_dist⟩
    -- x distance bound: x = lookahead - √η • v, so dist(x, m*) ≤ dist(la, m*) + ‖√η•v‖
    rcases n with _ | n
    · have hr4_lt_r := div_lt_self hr_pos (by norm_num : (1 : ℝ) < 4)
      exact Metric.mem_ball.mpr (lt_trans hs₀_x_dist hr4_lt_r)
    · -- For n+1: we know Ln(n) ≤ L₀, so velocity ≤ C_mov·√L₀ ≤ r/4
      have hLn_le_L₀ : Ln n ≤ L₀ := by
        have hcn := pow_le_one₀ hc_nonneg hc_le_one (n := n)
        have hLn_bound := (hinduction n).2.1
        nlinarith
      -- Need velocity bound at step n+1 from hypothesis at step n
      have hn_mem := (hinduction n).1
      have hLn_R : Ln n ≤ R ^ 2 := by
        linarith [mul_le_of_le_one_left hL₀_nonneg
          (pow_le_one₀ hc_nonneg hc_le_one (n := n))]
      have hv_bound_n := hvel_bound s₀ n hn_mem.1 hn_mem.2 hLn_R
      have hvel_small : C_mov * Real.sqrt (Ln n) ≤ r / 4 := by
        calc C_mov * Real.sqrt (Ln n)
            ≤ C_mov * Real.sqrt L₀ :=
              mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hLn_le_L₀) (le_of_lt hC_mov)
          _ ≤ r / 4 := hvel_comp
      have hx_eq : (nesterovSeqGen f η ρ s₀ (n + 1)).x =
          (nesterovSeqGen f η ρ s₀ (n + 1)).lookahead η -
          Real.sqrt η • (nesterovSeqGen f η ρ s₀ (n + 1)).v := by
        simp only [NesterovState.lookahead, add_sub_cancel_right]
      -- la_{n+1} distance bound: ≤ r/2 (tighter than hla_dist)
      have hla_n1_half : dist ((nesterovSeqGen f η ρ s₀ (n + 1)).lookahead η) m_star ≤
          r / 2 := by
        have hDn1 := (hinduction (n + 1)).2.2
        have hsum_bound1 : C_h * Real.sqrt η * Real.sqrt L₀ *
            (Finset.range (n + 1)).sum (fun k => Real.sqrt c ^ k) ≤ r / 4 := by
          have hle := partial_geom_series_bound (Real.sqrt c)
            (Real.sqrt_nonneg c) hsqrt_c_lt1 (n + 1)
          calc C_h * Real.sqrt η * Real.sqrt L₀ *
                (Finset.range (n + 1)).sum (fun k => Real.sqrt c ^ k)
              ≤ C_h * Real.sqrt η * Real.sqrt L₀ * (1 / (1 - Real.sqrt c)) := by
                apply mul_le_mul_of_nonneg_left hle
                apply mul_nonneg (mul_nonneg (le_of_lt hC_h) (Real.sqrt_nonneg _))
                  (Real.sqrt_nonneg _)
            _ = C_h * Real.sqrt η * Real.sqrt L₀ / (1 - Real.sqrt c) := by ring
            _ ≤ r / 4 := hdisp_bound
        linarith [hDn1, hs₀_la_dist]
      have hv_bound_small : ‖Real.sqrt η • (nesterovSeqGen f η ρ s₀ (n + 1)).v‖ ≤ r / 4 := by
        linarith [hv_bound_n, hvel_small]
      rw [Metric.mem_ball]
      calc dist (nesterovSeqGen f η ρ s₀ (n + 1)).x m_star
          = dist ((nesterovSeqGen f η ρ s₀ (n + 1)).lookahead η -
              Real.sqrt η • (nesterovSeqGen f η ρ s₀ (n + 1)).v) m_star := by
            rw [hx_eq]
        _ ≤ dist ((nesterovSeqGen f η ρ s₀ (n + 1)).lookahead η) m_star +
              ‖Real.sqrt η • (nesterovSeqGen f η ρ s₀ (n + 1)).v‖ := by
            rw [dist_eq_norm, dist_eq_norm]
            calc ‖(nesterovSeqGen f η ρ s₀ (n + 1)).lookahead η -
                    Real.sqrt η • (nesterovSeqGen f η ρ s₀ (n + 1)).v - m_star‖
                = ‖((nesterovSeqGen f η ρ s₀ (n + 1)).lookahead η - m_star) -
                    Real.sqrt η • (nesterovSeqGen f η ρ s₀ (n + 1)).v‖ := by
                  congr 1; abel
              _ ≤ ‖(nesterovSeqGen f η ρ s₀ (n + 1)).lookahead η - m_star‖ +
                    ‖Real.sqrt η • (nesterovSeqGen f η ρ s₀ (n + 1)).v‖ :=
                  norm_sub_le _ _
        _ ≤ r / 2 + r / 4 := by linarith [hla_n1_half, hv_bound_small]
        _ < r := by linarith
  refine ⟨fun n => (hinduction n).1, hball_contain, fun n => ?_⟩
  exact (hinduction (n + 1)).2.1


/-- Public theorem wrapper for `bootstrapTotalDisplacementProof`. -/
theorem bootstrap_total_displacement
    {d : ℕ} (_hd : 0 < d)
    -- The objective function
    (f : E d → ℝ)
    -- Parameters
    (L : ℝ≥0) (_hL : 0 < (L : ℝ))
    (μ' : ℝ) (hμ' : 0 < μ')
    (θ : ℝ) (hθ_pos : 0 < θ) (hθ_lt1 : θ < 1)
    (η : ℝ) (_hη : η = 1 / (L : ℝ)) (hη_pos : 0 < η)
    (hμη_lt1 : μ' * η < 1)
    (ρ : ℝ) (_hρ : ρ = (1 - Real.sqrt (μ' * η)) / (1 + Real.sqrt (μ' * η)))
    -- S = argmin set
    (S : Set (E d))
    (hM_argmin : S = argminSet f)
    -- Tubular neighborhood U
    (U : Set (E d))
    (_hTub : IsTubularNeighborhoodOfSubmanifold S U)
    -- Nearest-point projection
    (π : E d → E d)
    (_hπ_in_S : ∀ x, π x ∈ S)
    (_hπ_proj : ∀ x ∈ S, π x = x)
    (hπ_metric : ∀ x ∈ U, dist x (π x) = Metric.infDist x S)
    -- Tangent projector P
    (P : E d →L[ℝ] E d)
    -- Neighborhoods from `lyapunov_contraction`: Ω ⊂⊂ Ω⁺ ⊂⊂ U₊ ⊂ U
    (Ω : Set (E d)) (hΩ_open : IsOpen Ω) (hΩ_sub_U : Ω ⊆ U)
    -- R from `lyapunov_contraction`
    (R : ℝ) (hR : 0 < R)
    -- Base point
    (m_star : E d) (hm_star : m_star ∈ S) (hm_star_Ω : m_star ∈ Ω)
    -- Ψ continuity and vanishing at m⋆
    (hΨ_cont : ContinuousAt (psi f μ' S) m_star)
    (hΨ_zero : psi f μ' S m_star = 0)
    -- Quadratic growth (from `local_fiberwise_geometry`)
    (_hQG : ∀ x ∈ Ω, f x - fStar f ≥ μ' / 2 * (Metric.infDist x S) ^ 2)
    -- Lyapunov contraction (from `lyapunov_contraction`): whenever in Ω with L_n ≤ R²
    (hcontract : ∀ (x₁ : E d) (n : ℕ),
      let s := nesterovSeq f η ρ x₁ n
      let Ln := lyapunov P μ' π f η ρ x₁ n
      let Ln' := lyapunov P μ' π f η ρ x₁ (n + 1)
      let a := Real.sqrt (μ' * η)
      s.x ∈ Ω → s.lookahead η ∈ Ω → Ln ≤ R ^ 2 →
      Ln' ≤ (1 - (1 - θ) * a) * Ln)
    -- Motion bound on h_n (from `motion_bounds_curvature_error`)
    (C_h : ℝ) (hC_h : 0 < C_h)
    (hstep_bound : ∀ (x₁ : E d) (n : ℕ),
      let s := nesterovSeq f η ρ x₁ n
      let Ln := lyapunov P μ' π f η ρ x₁ n
      s.x ∈ Ω → s.lookahead η ∈ Ω → Ln ≤ R ^ 2 →
      ‖nesterovH f η ρ x₁ n‖ ≤ C_h * Real.sqrt η * Real.sqrt Ln)
    -- Motion bound on velocity (from `motion_bounds_curvature_error`)
    (C_mov : ℝ) (hC_mov : 0 < C_mov)
    (hvel_bound : ∀ (x₁ : E d) (n : ℕ),
      let s := nesterovSeq f η ρ x₁ n
      let s' := nesterovSeq f η ρ x₁ (n + 1)
      let Ln := lyapunov P μ' π f η ρ x₁ n
      s.x ∈ Ω → s.lookahead η ∈ Ω → Ln ≤ R ^ 2 →
      ‖Real.sqrt η • s'.v‖ ≤ C_mov * Real.sqrt Ln) :
    -- Conclusion: ∃ α > 0 with the bootstrap property
    ∃ (α : ℝ), 0 < α ∧
      ∀ x₁ ∈ Metric.ball m_star α ∩ U,
        -- (1) All iterates stay in Ω
        (∀ n : ℕ,
          (nesterovSeq f η ρ x₁ n).x ∈ Ω ∧
          (nesterovSeq f η ρ x₁ n).lookahead η ∈ Ω) ∧
        -- (2) All iterates remain in U
        (∀ n : ℕ, (nesterovSeq f η ρ x₁ n).x ∈ U) ∧
        -- (3) Geometric decay of Lyapunov function
        (∀ n : ℕ,
          let a := Real.sqrt (μ' * η)
          lyapunov P μ' π f η ρ x₁ (n + 1) ≤
            (1 - (1 - θ) * a) ^ (n + 1) * lyapunov P μ' π f η ρ x₁ 0) := by
  exact bootstrapTotalDisplacementProof (d := d) (_hd := _hd) (f := f) (L := L) (_hL := _hL)
    (μ' := μ') (hμ' := hμ') (θ := θ) (hθ_pos := hθ_pos) (hθ_lt1 := hθ_lt1) (η := η) (_hη := _hη)
    (hη_pos := hη_pos) (hμη_lt1 := hμη_lt1) (ρ := ρ) (_hρ := _hρ) (S := S) (hM_argmin := hM_argmin)
    (U := U) (_hTub := _hTub) (π := π) (_hπ_in_S := _hπ_in_S) (_hπ_proj := _hπ_proj)
    (hπ_metric := hπ_metric) (P := P) (Ω := Ω) (hΩ_open := hΩ_open) (hΩ_sub_U := hΩ_sub_U) (R := R)
    (hR := hR) (m_star := m_star) (hm_star := hm_star) (hm_star_Ω := hm_star_Ω) (hΨ_cont := hΨ_cont)
    (hΨ_zero := hΨ_zero) (_hQG := _hQG) (hcontract := hcontract) (C_h := C_h) (hC_h := hC_h)
    (hstep_bound := hstep_bound) (C_mov := C_mov) (hC_mov := hC_mov) (hvel_bound := hvel_bound)

/-- Public theorem wrapper for `bootstrapTotalDisplacementGenProof`. -/
theorem bootstrap_total_displacement_gen
    {d : ℕ}
    (f : E d → ℝ)
    (μ' : ℝ) (hμ' : 0 < μ')
    (θ : ℝ) (hθ_pos : 0 < θ) (hθ_lt1 : θ < 1)
    (η : ℝ) (hη_pos : 0 < η)
    (hμη_lt1 : μ' * η < 1)
    (ρ : ℝ)
    (S : Set (E d))
    (hM_argmin : S = argminSet f)
    (π : E d → E d)
    (P : E d →L[ℝ] E d)
    (Ω : Set (E d)) (hΩ_open : IsOpen Ω)
    (R : ℝ) (hR : 0 < R)
    (m_star : E d) (hm_star : m_star ∈ S) (hm_star_Ω : m_star ∈ Ω)
    -- Contraction (from lyapunov_contraction_gen)
    (hcontract : ∀ (s₀ : NesterovState d) (n : ℕ),
      let s := nesterovSeqGen f η ρ s₀ n
      s.x ∈ Ω → s.lookahead η ∈ Ω →
      lyapunovOfState P μ' π f η s ≤ R ^ 2 →
      lyapunovOfState P μ' π f η (nesterovSeqGen f η ρ s₀ (n + 1)) ≤
        (1 - (1 - θ) * Real.sqrt (μ' * η)) *
        lyapunovOfState P μ' π f η s)
    -- Step displacement bound
    (C_h : ℝ) (hC_h : 0 < C_h)
    (hstep_bound : ∀ (s₀ : NesterovState d) (n : ℕ),
      let s := nesterovSeqGen f η ρ s₀ n
      s.x ∈ Ω → s.lookahead η ∈ Ω →
      lyapunovOfState P μ' π f η s ≤ R ^ 2 →
      ‖stepDispOfState f η ρ s‖ ≤
        C_h * Real.sqrt η *
        Real.sqrt (lyapunovOfState P μ' π f η s))
    -- Velocity bound
    (C_mov : ℝ) (hC_mov : 0 < C_mov)
    (hvel_bound : ∀ (s₀ : NesterovState d) (n : ℕ),
      let s := nesterovSeqGen f η ρ s₀ n
      s.x ∈ Ω → s.lookahead η ∈ Ω →
      lyapunovOfState P μ' π f η s ≤ R ^ 2 →
      ‖Real.sqrt η • (nesterovSeqGen f η ρ s₀ (n + 1)).v‖ ≤
        C_mov * Real.sqrt (lyapunovOfState P μ' π f η s)) :
    ∃ (δ r_ball : ℝ), 0 < δ ∧ 0 < r_ball ∧
      Metric.ball m_star r_ball ⊆ Ω ∧
      ∀ s₀ : NesterovState d,
        s₀.x ∈ Metric.ball m_star δ →
        s₀.lookahead η ∈ Metric.ball m_star δ →
        lyapunovOfState P μ' π f η s₀ ≤ δ ^ 2 →
        -- (1) All iterates stay in Ω
        (∀ n : ℕ,
          (nesterovSeqGen f η ρ s₀ n).x ∈ Ω ∧
          (nesterovSeqGen f η ρ s₀ n).lookahead η ∈ Ω) ∧
        -- (2) Ball containment: iterates stay in ball(m_star, r_ball)
        (∀ n : ℕ,
          (nesterovSeqGen f η ρ s₀ n).x ∈ Metric.ball m_star r_ball ∧
          (nesterovSeqGen f η ρ s₀ n).lookahead η ∈ Metric.ball m_star r_ball) ∧
        -- (3) Geometric decay
        (∀ n : ℕ,
          let a := Real.sqrt (μ' * η)
          lyapunovOfState P μ' π f η (nesterovSeqGen f η ρ s₀ (n + 1)) ≤
            (1 - (1 - θ) * a) ^ (n + 1) *
            lyapunovOfState P μ' π f η s₀) := by
  exact bootstrapTotalDisplacementGenProof (d := d) (f := f) (μ' := μ') (hμ' := hμ') (θ := θ)
    (hθ_pos := hθ_pos) (hθ_lt1 := hθ_lt1) (η := η) (hη_pos := hη_pos) (hμη_lt1 := hμη_lt1) (ρ := ρ)
    (S := S) (hM_argmin := hM_argmin) (π := π) (P := P) (Ω := Ω) (hΩ_open := hΩ_open) (R := R)
    (hR := hR) (m_star := m_star) (hm_star := hm_star) (hm_star_Ω := hm_star_Ω)
    (hcontract := hcontract) (C_h := C_h) (hC_h := hC_h) (hstep_bound := hstep_bound)
    (C_mov := C_mov) (hC_mov := hC_mov) (hvel_bound := hvel_bound)

end PLAcceleratedNesterovLean
