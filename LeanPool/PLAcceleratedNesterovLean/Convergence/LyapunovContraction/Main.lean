/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import LeanPool.PLAcceleratedNesterovLean.Convergence.LyapunovContraction.Step1
import LeanPool.PLAcceleratedNesterovLean.Convergence.LyapunovContraction.Step2
import LeanPool.PLAcceleratedNesterovLean.Convergence.LyapunovContraction.Step3
import LeanPool.PLAcceleratedNesterovLean.Convergence.LyapunovContraction.AuxVar
import LeanPool.PLAcceleratedNesterovLean.Convergence.LyapunovContraction.FlatCaseHelper
import LeanPool.PLAcceleratedNesterovLean.Convergence.LyapunovContraction.FlatCaseArithmetic


/-!
# Lyapunov Contraction

After shrinking the neighborhood Ω and the energy radius R, one step of the
modified Nesterov scheme contracts the Lyapunov function by a factor 1 - a/2,
where a = √(μ'·η).
-/


noncomputable section

namespace PLAcceleratedNesterovLean

open scoped Topology NNReal
open Manifold


/-- **Lyapunov contraction.**

After shrinking Ω and R if necessary, whenever x_n, x'_n ∈ Ω and L_n ≤ R²:
  L_{n+1} ≤ (1 - (1-θ)·a) · L_n
and x_{n+1}, x'_{n+1} ∈ Ω⁺.

The budget-split parameter θ ∈ (0,1) controls what fraction of the contraction
rate a is consumed by perturbation absorption. When θ = 1/2 this gives (1 - a/2).
-/
private abbrev lyapunovContractionProof
    {d : ℕ} (_hd : 0 < d)
    -- The objective function
    (f : E d → ℝ)
    -- Parameters
    (L : ℝ≥0) (hL : 0 < (L : ℝ))
    (μ' : ℝ) (hμ' : 0 < μ')
    (θ : ℝ) (hθ_pos : 0 < θ) (hθ_lt1 : θ < 1)
    (η : ℝ) (hη : η = 1 / (L : ℝ)) (hη_pos : 0 < η)
    (ρ : ℝ) (hρ : ρ = (1 - Real.sqrt (μ' * η)) / (1 + Real.sqrt (μ' * η)))
    -- S = argmin set
    (S : Set (E d))
    (hM_argmin : S = argminSet f)
    -- Nearest-point projection
    (π : E d → E d)
    (_hπ_in_S : ∀ x, π x ∈ S)
    (_hπ_proj : ∀ x ∈ S, π x = x)
    -- Gradient vanishes on S
    (hgrad_zero : ∀ x ∈ S, gradient f x = 0)
    -- Tangent projector P = Dπ(m⋆)
    (P : E d →L[ℝ] E d)
    -- Base point
    (m_star : E d) (hm_star : m_star ∈ S)
    -- ε from `local_fiberwise_geometry`
    (ε : ℝ) (hε_pos : 0 < ε) (hε_bound : ε * η ≤ Real.sqrt (μ' * η))
    (hμη_lt1 : μ' * η < 1)
    -- Strong aiming on U₊ (from `local_fiberwise_geometry`)
    (U_plus : Set (E d))
    (hU_open : IsOpen U_plus)
    (hm_star_Up : m_star ∈ U_plus)
    -- Local smoothness on U₊
    (hf_diff_on : DifferentiableOn ℝ f U_plus)
    (hf_lip : LipschitzOnWith L (gradient f) U_plus)
    (hStrAim : ∀ x ∈ U_plus,
      @inner ℝ _ _ (gradient f x) (x - π x) ≥
        f x - fStar f + μ' / 2 * ‖x - π x‖ ^ 2)
    -- Hessian lower bound on U₊ (from `local_fiberwise_geometry`)
    (hHess_lower : ∀ x ∈ U_plus, ∀ ξ : E d,
      hessianQuadForm f x ξ ≥ -ε * ‖ξ‖ ^ 2)
    -- Normal Hessian on projection fibers: Dπ(π x) · e = 0 → e lies in normal space
    (_hπ_kills_normal : ∀ x ∈ U_plus,
      fderiv ℝ π (π x) (x - π x) = 0)
    -- P is self-adjoint (orthogonal projector property)
    (hP_self_adj : ∀ x y : E d, @inner ℝ _ _ (P x) y = @inner ℝ _ _ x (P y))
    -- P is idempotent (orthogonal projector property)
    (hP_idem : ∀ x : E d, P (P x) = P x)
    -- Segment estimate (from D²f ≽ -εI and C² regularity):
    --   ⟨∇f(x), x - z⟩ ≥ f(x) - f(z) - ε/2 · ‖x - z‖²
    (hSegment : ∀ x z : E d, x ∈ U_plus → z ∈ U_plus →
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 → (1 - t) • z + t • x ∈ U_plus) →
      @inner ℝ _ _ (gradient f x) (x - z) ≥
        f x - f z - ε / 2 * ‖x - z‖ ^ 2)
    -- Total perturbation absorption (curvature + projector-freezing error)
    -- δ_curv = curvature perturbation, proj_err = a·|⟨g, Pe⟩| from projector freezing
    -- R_abs is the energy/spatial radius: iterates must be in B(m⋆, R_abs) with Ln ≤ R_abs².
    (R_abs : ℝ) (hR_abs : 0 < R_abs)
    (h_curv_absorb : ∀ (x₁ : E d) (n : ℕ),
      (nesterovSeq f η ρ x₁ n).x ∈ Metric.ball m_star R_abs →
      (nesterovSeq f η ρ x₁ n).lookahead η ∈ Metric.ball m_star R_abs →
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
      let proj_err := a * |@inner ℝ _ _ gn (P en)|
      δ_curv + proj_err ≤ θ * a * Ln)
    :
    -- Conclusion: ∃ Ω, R (independent of starting point) such that contraction holds
    ∃ (Ω Ω_plus : Set (E d)) (R : ℝ),
      IsOpen Ω ∧ IsOpen Ω_plus ∧ 0 < R ∧
      m_star ∈ Ω ∧ Ω ⊆ Ω_plus ∧ Ω_plus ⊆ U_plus ∧
      -- For all starting points and iterations with the right preconditions
      ∀ (x₁ : E d) (n : ℕ),
        let s := nesterovSeq f η ρ x₁ n
        let s' := nesterovSeq f η ρ x₁ (n + 1)
        let Ln := lyapunov P μ' π f η ρ x₁ n
        let Ln' := lyapunov P μ' π f η ρ x₁ (n + 1)
        let a := Real.sqrt (μ' * η)
        s.x ∈ Ω → s.lookahead η ∈ Ω → Ln ≤ R ^ 2 →
        -- Contraction
        Ln' ≤ (1 - (1 - θ) * a) * Ln ∧
        -- Next iterates in Ω⁺
        s'.x ∈ Ω_plus ∧ s'.lookahead η ∈ Ω_plus := by
  /-
   Proof roadmap for the one-step contraction.

   Choose concentric neighborhoods Ω ⊂ Ω₊ ⊂ U₊ around m⋆ and an energy
   radius R.  For each iterate with xₙ, x'ₙ ∈ Ω and Lₙ ≤ R²:
   * descent gives f(x_{n+1}) ≤ f(x'_n) − (η/2)‖gₙ‖²;
   * the identity (1+a)ρ = 1−a rewrites the velocity update;
   * the normal terms complete the square into (1−a)/2 · ‖uₙ‖²;
   * the function values telescope to (1−a)(f(xₙ)−f⋆);
   * curvature and projector-freezing errors are absorbed using the θ-budget,
     producing Lₙ₊₁ ≤ (1 - (1-θ)a)Lₙ.
   -/
  -- ═══════════════════════════════════════════════════════════════
  -- Neighborhood construction
  -- ═══════════════════════════════════════════════════════════════
  -- Extract r₀ > 0 with B(m⋆, r₀) ⊆ U₊
  obtain ⟨r₀, hr₀_pos, hball_sub⟩ : ∃ r₀ > 0, Metric.ball m_star r₀ ⊆ U_plus := by
    exact Metric.isOpen_iff.mp hU_open m_star hm_star_Up
  -- Auxiliary inequalities for the chosen radii
  have hr₀9 : (0 : ℝ) < r₀ / 9 := by linarith
  have hR_min : (0 : ℝ) < min (r₀ / 9) R_abs := lt_min hr₀9 hR_abs
  -- Ω = B(m⋆, min(r₀/9, R_abs)) — ensures iterates are in B(m⋆, R_abs) for h_curv_absorb
  have hΩ_sub_r09 : Metric.ball m_star (min (r₀ / 9) R_abs) ⊆
      Metric.ball m_star (r₀ / 9) :=
    Metric.ball_subset_ball (min_le_left _ _)
  have hΩ_sub_Rabs : Metric.ball m_star (min (r₀ / 9) R_abs) ⊆
      Metric.ball m_star R_abs :=
    Metric.ball_subset_ball (min_le_right _ _)
  have hΩ_sub_Ωp : Metric.ball m_star (min (r₀ / 9) R_abs) ⊆
      Metric.ball m_star (2 * r₀ / 3) :=
    hΩ_sub_r09.trans (Metric.ball_subset_ball (by linarith))
  have h23_le : 2 * r₀ / 3 ≤ r₀ := by linarith
  have hΩp_sub_Up : Metric.ball m_star (2 * r₀ / 3) ⊆ U_plus :=
    (Metric.ball_subset_ball h23_le).trans hball_sub
  -- Provide the existential witnesses:
  --   Ω   := B(m⋆, min(r₀/9, R_abs))
  --   Ω₊  := B(m⋆, 2r₀/3)
  --   R   := min(r₀/9, R_abs)
  refine ⟨Metric.ball m_star (min (r₀ / 9) R_abs),
          Metric.ball m_star (2 * r₀ / 3),
          min (r₀ / 9) R_abs,
          Metric.isOpen_ball,
          Metric.isOpen_ball,
          hR_min,
          Metric.mem_ball_self hR_min,
          hΩ_sub_Ωp,
          hΩp_sub_Up,
          ?_⟩
  -- ═══════════════════════════════════════════════════════════════
  -- Main contraction argument
  -- ═══════════════════════════════════════════════════════════════
  intro x₁ n sn sn1 Ln Ln' a hx_in hx'_in hLn_bound
  -- Additional convenient abbreviations
  let x'n := sn.lookahead η
  let gn  := gradient f x'n
  let en  := normalDisp π f η ρ x₁ n
  let un  := auxVar P μ' π f η ρ x₁ n
  -- ─────────────────────────────────────────────────────────────
  -- Step 1 (Descent): f(x_{n+1}) ≤ f(x'_n) − (η/2)·‖g_n‖²
  -- ─────────────────────────────────────────────────────────────
  have h_descent : f sn1.x ≤ f x'n - η / 2 * ‖gn‖ ^ 2 := by
    -- sn1.x = x'n - η • gn by definition of nesterovStep/nesterovSeq
    have hx_eq : sn1.x = x'n - η • gn := rfl
    rw [hx_eq]
    have hx'_Up : x'n ∈ U_plus := hΩp_sub_Up (hΩ_sub_Ωp hx'_in)
    have hx'_r09 : dist x'n m_star < r₀ / 9 :=
      Metric.mem_ball.mp (hΩ_sub_r09 hx'_in)
    have hg_zero' : gradient f m_star = 0 := hgrad_zero m_star hm_star
    have hgrad_lip' : ‖gn‖ ≤ (↑L : ℝ) * dist x'n m_star := by
      have h := hf_lip.dist_le_mul x'n hx'_Up m_star hm_star_Up
      rwa [hg_zero', dist_zero_right] at h
    have hseg_x'n : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        x'n + t • (-(((1 : ℝ) / (L : ℝ)) • gradient f x'n)) ∈ U_plus := by
      intro t ht0 ht1
      apply hball_sub; rw [Metric.mem_ball]
      have h_step_bound : dist (x'n + t • (-(((1 : ℝ) / (↑L : ℝ)) • gn))) x'n ≤
          dist x'n m_star := by
        rw [dist_eq_norm,
            show (x'n + t • (-(((1 : ℝ) / (↑L : ℝ)) • gn))) - x'n =
                t • (-(((1 : ℝ) / (↑L : ℝ)) • gn)) from by abel,
            norm_smul, norm_neg, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg ht0, Real.norm_eq_abs,
            abs_of_pos (div_pos one_pos hL)]
        calc t * ((1 : ℝ) / (↑L : ℝ) * ‖gn‖)
            ≤ 1 * ((1 : ℝ) / (↑L : ℝ) * ((↑L : ℝ) * dist x'n m_star)) :=
              mul_le_mul ht1
                (mul_le_mul_of_nonneg_left hgrad_lip'
                  (le_of_lt (div_pos one_pos hL)))
                (mul_nonneg (le_of_lt (div_pos one_pos hL)) (norm_nonneg _))
                one_pos.le
          _ = dist x'n m_star := by
              rw [one_mul, ← mul_assoc, one_div_mul_cancel (ne_of_gt hL), one_mul]
      calc dist (x'n + t • (-(((1 : ℝ) / (↑L : ℝ)) • gn))) m_star
          ≤ dist (x'n + t • (-(((1 : ℝ) / (↑L : ℝ)) • gn))) x'n + dist x'n m_star :=
            dist_triangle _ _ _
        _ ≤ 2 * dist x'n m_star := by linarith [h_step_bound]
        _ < 2 * (r₀ / 9) := by linarith [hx'_r09]
        _ < r₀ := by linarith
    exact lsmooth_descent_at f L hL hU_open hf_diff_on hf_lip x'n hx'_Up hseg_x'n η hη
  -- ─────────────────────────────────────────────────────────────
  -- Step 2 (Parameter identities)
  -- ─────────────────────────────────────────────────────────────
  have ha_pos : 0 < a := by
    exact Real.sqrt_pos_of_pos (mul_pos hμ' hη_pos)
  have ha_lt1 : a < 1 := by
    have hle : (0 : ℝ) ≤ μ' * η := le_of_lt (mul_pos hμ' hη_pos)
    calc a = Real.sqrt (μ' * η) := rfl
      _ < Real.sqrt 1 := Real.sqrt_lt_sqrt hle (by linarith)
      _ = 1 := Real.sqrt_one
  have h_rho_id : (1 + a) * ρ = 1 - a := by
    have h1a : (0 : ℝ) < 1 + a := by linarith
    exact rho_identity a ρ h1a.ne' hρ
  -- ─────────────────────────────────────────────────────────────
  -- Step 3 (Complete the square for normal terms)
  --   ((1-a)/2)·‖v‖² + (1-a)·√μ'·⟨v,e⟩ + ((1-a)·μ'/2)·‖e‖²
  --     = ((1-a)/2)·‖v + √μ'·e‖²   =   ((1-a)/2)·‖uₙ‖²
  -- ─────────────────────────────────────────────────────────────
  have h_complete_sq : ∀ (v e : E d),
      (1 - a) / 2 * ‖v‖ ^ 2 +
      (1 - a) * Real.sqrt μ' * @inner ℝ _ _ v e +
      (1 - a) * (Real.sqrt μ') ^ 2 / 2 * ‖e‖ ^ 2 =
      (1 - a) / 2 * ‖v + Real.sqrt μ' • e‖ ^ 2 := by
    intro v e
    exact complete_square_normal v e (1 - a) (Real.sqrt μ') (by linarith)
  -- ─────────────────────────────────────────────────────────────
  -- Step 4 (Function-value telescoping)
  --   (f'−f⋆) − (1−a)(f'−f) − a(f'−f⋆) = (1−a)(f−f⋆)
  -- ─────────────────────────────────────────────────────────────
  have h_func : ∀ f' fv : ℝ,
      (f' - fStar f) - (1 - a) * (f' - fv) - a * (f' - fStar f) =
      (1 - a) * (fv - fStar f) :=
    fun f' fv => function_value_collection f' fv (fStar f) a
  -- ─────────────────────────────────────────────────────────────
  -- Step 5 (Perturbation expansion + Cauchy–Schwarz)
  --   ‖w + c·ξ‖² = ‖w‖² + 2c⟨w,ξ⟩ + c²‖ξ‖²
  --   |⟨w,ξ⟩| ≤ ‖w‖·‖ξ‖
  -- ─────────────────────────────────────────────────────────────
  have h_perturb : ∀ (w ξ : E d) (c : ℝ),
      ‖w + c • ξ‖ ^ 2 =
      ‖w‖ ^ 2 + 2 * c * @inner ℝ _ _ w ξ + c ^ 2 * ‖ξ‖ ^ 2 :=
    fun w ξ c => perturbation_expansion w ξ c
  have h_cs : ∀ (w ξ : E d),
      |@inner ℝ _ _ w ξ| ≤ ‖w‖ * ‖ξ‖ :=
    fun w ξ => inner_abs_le_norm_mul w ξ
  -- ─────────────────────────────────────────────────────────────
  -- Step 6 (Velocity coefficient bounds from Step 1 helpers)
  -- ─────────────────────────────────────────────────────────────
  have h_vel_coeff : ∀ (εη : ℝ), 0 ≤ εη → εη ≤ a →
      (1 - a) ^ 2 + εη * (1 - a) ≤ 1 - a :=
    fun εη hεη hb => velocity_normal_coeff a εη (le_of_lt ha_pos) (le_of_lt ha_lt1) hεη hb
  have h_tang_coeff : (1 - a) * (1 + a) ≤ (1 + a) ^ 2 :=
    tangential_coeff a (le_of_lt ha_pos)
  -- ═══════════════════════════════════════════════════════════════
  -- Shared facts (used by multiple cases)
  -- ═══════════════════════════════════════════════════════════════
  have hg_zero_mstar : gradient f m_star = 0 := hgrad_zero m_star hm_star
  have hηL : η * (L : ℝ) = 1 := by rw [hη]; field_simp
  have hx'_ball_r09 : dist x'n m_star < r₀ / 9 :=
    lt_of_lt_of_le (Metric.mem_ball.mp hx'_in) (min_le_left _ _)
  have hρ_pos : 0 < ρ := by rw [hρ]; apply div_pos <;> linarith
  -- ═══════════════════════════════════════════════════════════════
  -- Assemble the three conclusions
  -- ═══════════════════════════════════════════════════════════════
  refine ⟨?contraction, ?x_next_in, ?x'_next_in⟩
  case contraction =>
    /- Combining Steps 1–6:
       Descent (Step 1) bounds f(x_{n+1}).
       The ρ-identity (Step 2) rewrites the velocity recursion.
       Completing the square (Step 3) recombines normal terms → (1−a)/2·‖uₙ‖².
       Function telescoping (Step 4) yields (1−a)(f(xₙ)−f⋆).
       Perturbation + Cauchy–Schwarz (Step 5) absorb ξₙ when R is small.
       Velocity bounds (Step 6) confirm coefficient contraction.
       Together:  L_{n+1} ≤ (1 − a/2) · Lₙ. -/
    -- Membership for applying strong aiming and Hessian bound
    have hx'n_Up : x'n ∈ U_plus := hΩp_sub_Up (hΩ_sub_Ωp hx'_in)
    -- Strong aiming: ⟨∇f(x'_n), e_n⟩ ≥ f(x'_n) - f⋆ + μ'/2 ‖e_n‖²
    have h_aim : @inner ℝ _ _ (gradient f x'n) (x'n - π x'n) ≥
        f x'n - fStar f + μ' / 2 * ‖x'n - π x'n‖ ^ 2 :=
      hStrAim x'n hx'n_Up
    -- f-value descent from Step 1
    have h_f_upper : f sn1.x - fStar f ≤ f x'n - fStar f - η / 2 * ‖gn‖ ^ 2 := by
      linarith [h_descent]
    -- Hessian perturbation control at x'_n
    have h_hess_x' : ∀ ξ : E d, hessianQuadForm f x'n ξ ≥ -ε * ‖ξ‖ ^ 2 :=
      hHess_lower x'n hx'n_Up
    -- ══════════════ Nonnegativity infrastructure ══════════════
    -- BddBelow for fStar
    have hmin : ∀ y, f m_star ≤ f y := by
      intro y; exact (hM_argmin ▸ hm_star : m_star ∈ argminSet f) y
    have hbdd : BddBelow (Set.range f) :=
      ⟨f m_star, by rintro _ ⟨x, rfl⟩; exact hmin x⟩
    have hgap_nn : 0 ≤ f sn.x - fStar f :=
      sub_nonneg.mpr (ciInf_le hbdd sn.x)
    have hgap'_nn : 0 ≤ f sn1.x - fStar f :=
      sub_nonneg.mpr (ciInf_le hbdd sn1.x)
    -- Parameter positivity
    have h1a_pos : (0 : ℝ) < 1 + a := by linarith
    have h1a_ne : (1 + a : ℝ) ≠ 0 := ne_of_gt h1a_pos
    have h1ma_pos : (0 : ℝ) < 1 - a := by linarith
    have h1ma_ne : (1 - a : ℝ) ≠ 0 := ne_of_gt h1ma_pos
    -- λ = (1+a)²/(2(1-a)) > 0
    have hlam_pos : (0 : ℝ) < (1 + a) ^ 2 / (2 * (1 - a)) :=
      div_pos (sq_pos_of_pos h1a_pos) (by linarith)
    -- Ln ≥ 0
    have hLn_nn : 0 ≤ Ln := by
      change 0 ≤ lyapunov P μ' π f η ρ x₁ n
      simp only [lyapunov]
      have hlam_nn : 0 ≤ (1 + Real.sqrt (μ' * η)) ^ 2 / (2 * (1 - Real.sqrt (μ' * η))) :=
        le_of_lt hlam_pos
      have h1 := sq_nonneg ‖auxVar P μ' π f η ρ x₁ n‖
      have h2 := mul_nonneg hlam_nn (sq_nonneg ‖P (nesterovSeq f η ρ x₁ n).v‖)
      linarith
    -- ══════════════ Tangential velocity identity ══════════════
    -- P is a CLM, so P(sn1.v) = ρ • (P sn.v - √η • P gn)
    have hPv1 : P sn1.v = ρ • (P sn.v - Real.sqrt η • P gn) := by
      change P (ρ • (sn.v - Real.sqrt η • gn)) = ρ • (P sn.v - Real.sqrt η • P gn)
      rw [map_smul, map_sub, map_smul]
    -- λ‖P sn1.v‖² = ((1-a)/2) ‖P sn.v - √η • P gn‖²
    have hTn1_eq : (1 + a) ^ 2 / (2 * (1 - a)) * ‖P sn1.v‖ ^ 2 =
        (1 - a) / 2 * ‖P sn.v - Real.sqrt η • P gn‖ ^ 2 := by
      rw [hPv1, norm_smul, Real.norm_eq_abs, abs_of_pos hρ_pos, mul_pow, ← mul_assoc]
      congr 1
      exact lambda_rho_sq a ρ _ h1a_ne h1ma_ne hρ rfl
    -- ══════════════ Aiming gives function descent bound ══════════════
    -- From descent + aiming: Fn' ≤ ⟨gn, en⟩ - μ'/2 ‖en‖² - η/2 ‖gn‖²
    have hFn'_bound : f sn1.x - fStar f ≤
        @inner ℝ _ _ gn (x'n - π x'n) - μ' / 2 * ‖x'n - π x'n‖ ^ 2 -
        η / 2 * ‖gn‖ ^ 2 :=
      function_descent_with_aiming _ _ _ _ _ _ _ h_f_upper h_aim
    -- ══════════════ Lyapunov decomposition ══════════════
    -- Abbreviate the Lyapunov components at steps n and n+1.
    set lam := (1 + a) ^ 2 / (2 * (1 - a)) with hlam_def
    set Fn  := f sn.x - fStar f  with hFn_def
    set Un  := ‖un‖ ^ 2           with hUn_def
    set Tn  := lam * ‖P sn.v‖ ^ 2 with hTn_def
    set un1 := auxVar P μ' π f η ρ x₁ (n + 1) with hun1_def
    set Fn1 := f sn1.x - fStar f   with hFn1_def
    set Un1 := ‖un1‖ ^ 2            with hUn1_def
    set Tn1 := lam * ‖P sn1.v‖ ^ 2  with hTn1_def
    -- Lyapunov decomposition identities
    have hLn_eq : Ln = Fn + Un / 2 + Tn := by
      change lyapunov P μ' π f η ρ x₁ n = Fn + Un / 2 + Tn
      unfold lyapunov; rfl
    have hLn'_eq : Ln' = Fn1 + Un1 / 2 + Tn1 := by
      change lyapunov P μ' π f η ρ x₁ (n + 1) = Fn1 + Un1 / 2 + Tn1
      unfold lyapunov; rfl
    -- Nonnegativity
    have hTn_nn  : 0 ≤ Tn  := mul_nonneg (le_of_lt hlam_pos) (sq_nonneg _)
    have hTn1_nn : 0 ≤ Tn1 := mul_nonneg (le_of_lt hlam_pos) (sq_nonneg _)
    -- ══════════════ Tangential energy identity ══════════════
    -- hTn1_eq: lam * ‖P sn1.v‖² = (1-a)/2 * ‖Pv - √η·Pg‖²
    -- Restate in terms of Tn1:
    have hTn1_val : Tn1 = (1 - a) / 2 * ‖P sn.v - Real.sqrt η • P gn‖ ^ 2 := by
      rw [hTn1_def]; exact hTn1_eq
    -- Expand ‖Pv - √η·Pg‖² for later use:
    have h_expand : ‖P sn.v - Real.sqrt η • P gn‖ ^ 2 =
        ‖P sn.v‖ ^ 2 - 2 * @inner ℝ _ _ (P sn.v) (Real.sqrt η • P gn) +
        ‖Real.sqrt η • P gn‖ ^ 2 := by rw [norm_sub_sq_real]
    have h_inner : @inner ℝ _ _ (P sn.v) (Real.sqrt η • P gn) =
        Real.sqrt η * @inner ℝ _ _ (P sn.v) (P gn) := by rw [inner_smul_right]
    have h_norm_smul : ‖Real.sqrt η • P gn‖ ^ 2 = η * ‖P gn‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
          Real.sq_sqrt (le_of_lt hη_pos)]
    -- λ ≥ 1/2 (ensures ‖Pv‖² ≤ 2·Tn, used for coercivity bounds)
    have hlam_ge_half : (1 : ℝ) / 2 ≤ lam := by
      rw [hlam_def]
      have h2ma : (0 : ℝ) < 2 * (1 - a) := by linarith
      rw [div_le_div_iff₀ two_pos h2ma]
      have h_asq := sq_nonneg a
      linarith
    -- ── Contraction assembly ──
    -- Two-step: (A) L_{n+1} ≤ (1-a)·L_n + δ, (B) δ ≤ (a/2)·L_n → L_{n+1} ≤ (1-a/2)·L_n

    -- ── Define intermediate quantities ──
    let ξn := curvatureError (↑P) π f η ρ x₁ n
    let wn := un1 - Real.sqrt μ' • ξn
    -- ── AuxVar decomposition: u_{n+1} = w_n + √μ'·ξ_n ──
    have h_un1_eq : un1 = wn + Real.sqrt μ' • ξn := by
      change un1 = (un1 - Real.sqrt μ' • ξn) + Real.sqrt μ' • ξn
      abel
    -- ── Perturbation expansion ──
    have h_Un1_expand : Un1 =
        ‖wn‖ ^ 2 + 2 * Real.sqrt μ' * @inner ℝ _ _ wn ξn +
        (Real.sqrt μ') ^ 2 * ‖ξn‖ ^ 2 := by
      change ‖un1‖ ^ 2 = _
      rw [h_un1_eq]
      exact perturbation_expansion wn ξn (Real.sqrt μ')
    -- ── Curvature perturbation δ ──
    set δ_curv := Real.sqrt μ' * @inner ℝ _ _ wn ξn +
                  (Real.sqrt μ') ^ 2 / 2 * ‖ξn‖ ^ 2 with hδ_def
    -- ── Perturbation splitting: Un1/2 = ‖wn‖²/2 + δ_curv ──
    have h_Un1_half : Un1 / 2 = ‖wn‖ ^ 2 / 2 + δ_curv := by
      rw [h_Un1_expand]; ring
    -- ── Flat-case assembly (Step A core) ──
    -- This is the heart of the Lyapunov contraction in the flat case.
    -- Mathematically: the auxiliary variable recursion gives
    --   w_n = (1-a)·P⊥v_n + √μ'·e_n - √η·P⊥g_n
    -- and combining with descent, aiming, and the tangential identity yields
    --   F_{n+1} + ‖w_n‖²/2 + T_{n+1} ≤ (1-a)·(F_n + U_n/2 + T_n)
    have h_flat : Fn1 + ‖wn‖ ^ 2 / 2 + Tn1 ≤
        (1 - a) * (Fn + Un / 2 + Tn) + a * abs (@inner ℝ _ _ gn (P en)) := by
      -- ═══ A: wn decomposition via auxVar_recursion ═══
      have hwn_eq : (wn : E d) = (1 - a) • (sn.v - P sn.v) +
          Real.sqrt μ' • en - Real.sqrt η • (gn - P gn) := by
        change un1 - Real.sqrt μ' • ξn = _
        have h_av := auxVar_recursion P μ' η ρ π f x₁ n hρ ha_pos hη_pos hμ'
        have : (un1 : E d) = ((1 - a) • (sn.v - P sn.v) + Real.sqrt μ' • en -
            Real.sqrt η • (gn - P gn)) + Real.sqrt μ' • ξn := by
          change auxVar P μ' π f η ρ x₁ (n + 1) = _; exact h_av
        rw [this]; abel
      -- ═══ B: Projector-freezing decomposition ═══
      -- ⟨g, e⟩ = ⟨P⊥g, e⟩ + ⟨g, Pe⟩ (via self-adjointness of P)
      have h_ipGE_decomp : @inner ℝ _ _ gn en =
          @inner ℝ _ _ (gn - P gn) en + @inner ℝ _ _ gn (P en) := by
        have hsplit : gn = (gn - P gn) + P gn := by abel
        conv_lhs => rw [hsplit]
        rw [inner_add_left, hP_self_adj gn en]
      have hG_pyth := pythagorean_proj P hP_self_adj hP_idem gn
      have hV_pyth := pythagorean_proj P hP_self_adj hP_idem sn.v
      have h_ip_decomp := inner_proj_decomp P hP_self_adj hP_idem gn sn.v
      -- ═══ C: Explicit conversion of hFn'_bound to use en ═══
      -- (en is definitionally x'n - π x'n, so this is just type-checking)
      have hFn1_le : Fn1 ≤
          @inner ℝ _ _ gn en - μ' / 2 * ‖en‖ ^ 2 -
          η / 2 * ‖gn‖ ^ 2 := hFn'_bound
      -- ═══ D: Norm expansions ═══
      have h_wn_sq : ‖wn‖ ^ 2 =
          (1 - a) ^ 2 * ‖sn.v - P sn.v‖ ^ 2 + μ' * ‖en‖ ^ 2 +
          η * ‖gn - P gn‖ ^ 2 +
          2 * (1 - a) * Real.sqrt μ' * @inner ℝ _ _ (sn.v - P sn.v) en -
          2 * (1 - a) * Real.sqrt η * @inner ℝ _ _ (sn.v - P sn.v) (gn - P gn) -
          2 * Real.sqrt μ' * Real.sqrt η * @inner ℝ _ _ en (gn - P gn) := by
        rw [hwn_eq]
        exact norm_three_term_sq _ _ _ _ _ _ (le_of_lt hμ') (le_of_lt hη_pos)
      have h_un_eq : Un = ‖sn.v - P sn.v‖ ^ 2 + μ' * ‖en‖ ^ 2 +
          2 * Real.sqrt μ' * @inner ℝ _ _ (sn.v - P sn.v) en := by
        change ‖un‖ ^ 2 = _
        exact norm_two_term_sq _ _ _ (le_of_lt hμ')
      have h_un_eq' : Un = ‖sn.v - P sn.v‖ ^ 2 +
          2 * Real.sqrt μ' * @inner ℝ _ _ (sn.v - P sn.v) en + μ' * ‖en‖ ^ 2 := by
        linarith
      have h_Tn1_exp : Tn1 = (1 - a) / 2 * ‖P sn.v‖ ^ 2 -
          (1 - a) * Real.sqrt η * @inner ℝ _ _ (P sn.v) (P gn) +
          (1 - a) / 2 * η * ‖P gn‖ ^ 2 := by
        rw [hTn1_val, h_expand, h_inner, h_norm_smul]; ring
      have h_sqrt_prod : Real.sqrt μ' * Real.sqrt η = a := by
        change Real.sqrt μ' * Real.sqrt η = Real.sqrt (μ' * η)
        rw [← Real.sqrt_mul (le_of_lt hμ')]
      -- Key coefficient identity: 2·√μ'·√η = 2·a (for norm simplification)
      have h2a : 2 * Real.sqrt μ' * Real.sqrt η = 2 * a := by
        have : (2 : ℝ) * Real.sqrt μ' * Real.sqrt η =
            2 * (Real.sqrt μ' * Real.sqrt η) := by ring
        rw [this, h_sqrt_prod]
      -- ═══ E: ‖wn‖²/2 with √μ'·√η replaced by a ═══
      have h_wn_half : ‖wn‖ ^ 2 / 2 =
          (1 - a) ^ 2 / 2 * ‖sn.v - P sn.v‖ ^ 2 + μ' / 2 * ‖en‖ ^ 2 +
          η / 2 * ‖gn - P gn‖ ^ 2 +
          (1 - a) * Real.sqrt μ' * @inner ℝ _ _ (sn.v - P sn.v) en -
          (1 - a) * Real.sqrt η * @inner ℝ _ _ (sn.v - P sn.v) (gn - P gn) -
          a * @inner ℝ _ _ en (gn - P gn) := by
        rw [h_wn_sq, h2a]; ring
      -- ═══ G: Segment estimate ═══
      have hxn_Up : sn.x ∈ U_plus := hΩp_sub_Up (hΩ_sub_Ωp hx_in)
      have h_path : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
          (1 - t) • sn.x + t • x'n ∈ U_plus := by
        intro t ht0 ht1
        exact hΩp_sub_Up (hΩ_sub_Ωp
          ((convex_ball m_star (min (r₀ / 9) R_abs)) hx_in hx'_in
            (by linarith : (0 : ℝ) ≤ 1 - t) ht0 (by linarith : (1 : ℝ) - t + t = 1)))
      have h_seg_raw := hSegment x'n sn.x hx'n_Up hxn_Up h_path
      have h_diff_eq : x'n - sn.x = Real.sqrt η • sn.v := by
        change sn.x + Real.sqrt η • sn.v - sn.x = _; abel
      have h_diff_sq : ‖x'n - sn.x‖ ^ 2 = η * ‖sn.v‖ ^ 2 := by
        rw [h_diff_eq, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (Real.sqrt_nonneg η), mul_pow,
            Real.sq_sqrt (le_of_lt hη_pos)]
      have h_inner_diff : @inner ℝ _ _ gn (x'n - sn.x) =
          Real.sqrt η * @inner ℝ _ _ gn sn.v := by
        rw [h_diff_eq, inner_smul_right]
      -- ═══ H: Apply flat_case_arithmetic ═══
      -- Set up intermediate quantities for the arithmetic lemma
      set Fnprime := f x'n - fStar f with hFnprime_def
      -- Descent bound: Fn1 ≤ Fnprime - η/2·(‖Pg‖² + ‖P⊥g‖²)
      have hFn1_descent : Fn1 ≤ Fnprime - η / 2 * (‖P gn‖ ^ 2 + ‖gn - P gn‖ ^ 2) := by
        have h_mid : Fn1 ≤ Fnprime - η / 2 * ‖gn‖ ^ 2 := by linarith [hFn'_bound, h_aim]
        have h_eq : η / 2 * ‖gn‖ ^ 2 = η / 2 * (‖P gn‖ ^ 2 + ‖gn - P gn‖ ^ 2) := by
          rw [hG_pyth]
        linarith
      -- Segment: √η·(⟨Pg,Pv⟩ + ⟨P⊥g,P⊥v⟩) ≥ Fnprime - Fn - εη/2·(‖Pv‖² + ‖P⊥v‖²)
      have h_segment_arith :
          Real.sqrt η * (@inner ℝ _ _ (P gn) (P sn.v) +
            @inner ℝ _ _ (gn - P gn) (sn.v - P sn.v)) ≥
          Fnprime - Fn - ε * η / 2 * (‖P sn.v‖ ^ 2 + ‖sn.v - P sn.v‖ ^ 2) := by
        -- From segment estimate: ⟨gn, x'n - sn.x⟩ ≥ f(x'n) - f(sn.x) - ε/2·‖x'n-sn.x‖²
        have h1 := h_seg_raw
        rw [h_inner_diff, h_diff_sq] at h1
        -- h1: √η·⟨gn,sn.v⟩ ≥ Fnprime - Fn - εη/2·‖sn.v‖²
        -- Use ip_decomp and V_pyth to rewrite
        rw [h_ip_decomp, hV_pyth] at h1
        linarith
      -- Aiming: ⟨P⊥g, en⟩ ≥ Fnprime + μ'/2·‖en‖² − |⟨g, Pe⟩| (projector-freezing error)
      have h_aiming_arith : @inner ℝ _ _ (gn - P gn) en ≥
          Fnprime + μ' / 2 * ‖en‖ ^ 2 - abs (@inner ℝ _ _ gn (P en)) := by
        -- Convert h_aim to use set-abbreviations gn, en, Fnprime
        have h_aim' : @inner ℝ _ _ gn en ≥ Fnprime + μ' / 2 * ‖en‖ ^ 2 := h_aim
        have hle := le_abs_self (@inner ℝ _ _ gn (P en))
        linarith [h_ipGE_decomp]
      -- wn norm identity (with √μ'·√η = a)
      have h_inner_comm_en_ppg : @inner ℝ _ _ en (gn - P gn) =
          @inner ℝ _ _ (gn - P gn) en := real_inner_comm _ _
      have hwn_sq_arith : ‖wn‖ ^ 2 =
          (1 - a) ^ 2 * ‖sn.v - P sn.v‖ ^ 2 + μ' * ‖en‖ ^ 2 +
          η * ‖gn - P gn‖ ^ 2 +
          2 * (1 - a) * Real.sqrt μ' * @inner ℝ _ _ (sn.v - P sn.v) en -
          2 * (1 - a) * Real.sqrt η * @inner ℝ _ _ (gn - P gn) (sn.v - P sn.v) -
          2 * a * @inner ℝ _ _ (gn - P gn) en := by
        rw [h_wn_sq, h2a, h_inner_comm_en_ppg]
        have h_ic3 : @inner ℝ _ _ (sn.v - P sn.v) (gn - P gn) =
            @inner ℝ _ _ (gn - P gn) (sn.v - P sn.v) := real_inner_comm _ _
        rw [h_ic3]
      -- Tn1 identity (matching flat_case_arithmetic parameter order)
      have hTn1_arith : Tn1 = (1 - a) / 2 * ‖P sn.v‖ ^ 2 -
          (1 - a) * Real.sqrt η * @inner ℝ _ _ (P gn) (P sn.v) +
          (1 - a) * η / 2 * ‖P gn‖ ^ 2 := by
        have h_PgPv_comm : @inner ℝ _ _ (P sn.v) (P gn) =
            @inner ℝ _ _ (P gn) (P sn.v) := real_inner_comm _ _
        rw [h_Tn1_exp, h_PgPv_comm]; ring
      -- Tn identity
      have hTn_arith : Tn = (1 + a) ^ 2 / (2 * (1 - a)) * ‖P sn.v‖ ^ 2 := by
        rw [hTn_def, hlam_def]
      -- Fnprime ≥ 0
      have hFnprime_nn : 0 ≤ Fnprime := by
        change 0 ≤ f x'n - fStar f
        exact sub_nonneg.mpr (ciInf_le hbdd x'n)
      -- Un nonnegativity
      have hUn_nn : 0 ≤ Un := by
        change 0 ≤ ‖un‖ ^ 2; exact sq_nonneg _
      -- Apply the arithmetic lemma
      have hpe_abs_nn : (0 : ℝ) ≤ abs (@inner ℝ _ _ gn (P en)) := abs_nonneg _
      exact flat_case_arithmetic a ha_pos ha_lt1
        η μ' (Real.sqrt μ') (Real.sqrt η)
        hη_pos hμ' (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        (Real.sq_sqrt (le_of_lt hμ')) (Real.sq_sqrt (le_of_lt hη_pos))
        h_sqrt_prod
        (ε * η) (mul_nonneg (le_of_lt hε_pos) (le_of_lt hη_pos)) hε_bound
        Fn Fn1 Fnprime hgap_nn hgap'_nn hFnprime_nn
        (‖P sn.v‖ ^ 2) (‖sn.v - P sn.v‖ ^ 2) (‖P gn‖ ^ 2) (‖gn - P gn‖ ^ 2) (‖en‖ ^ 2)
        (sq_nonneg _) (sq_nonneg _) (sq_nonneg _) (sq_nonneg _) (sq_nonneg _)
        (@inner ℝ _ _ (gn - P gn) en) (@inner ℝ _ _ (P gn) (P sn.v))
        (@inner ℝ _ _ (gn - P gn) (sn.v - P sn.v)) (@inner ℝ _ _ (sn.v - P sn.v) en)
        (abs (@inner ℝ _ _ gn (P en))) hpe_abs_nn
        hFn1_descent h_segment_arith h_aiming_arith
        (‖wn‖ ^ 2) hwn_sq_arith
        Un h_un_eq'
        Tn1 hTn1_arith
        Tn hTn_arith
    -- ── Total perturbation absorption (Step B) ──
    -- Curvature (ξ_n) + projector-freezing (|⟨g, Pe⟩|) terms are absorbed
    -- by shrinking Ω and R. The hypothesis h_curv_absorb provides this.
    -- Derive Ln ≤ R_abs² from Ln ≤ (min(r₀/9, R_abs))² ≤ R_abs²
    have hLn_le_Rabs : Ln ≤ R_abs ^ 2 := by
      calc Ln ≤ (min (r₀ / 9) R_abs) ^ 2 := hLn_bound
        _ ≤ R_abs ^ 2 := by
          apply pow_le_pow_left₀ (le_min (le_of_lt hr₀9) (le_of_lt hR_abs))
            (min_le_right _ _)
    set proj_err_n := a * abs (@inner ℝ _ _ gn (P en)) with hproj_err_def
    have h_absorb : δ_curv + proj_err_n ≤ θ * a * Ln :=
      h_curv_absorb x₁ n (hΩ_sub_Rabs hx_in) (hΩ_sub_Rabs hx'_in)
        hLn_le_Rabs
    -- ── Final assembly ──
    apply two_step_contraction_general a θ Ln Ln' (δ_curv + proj_err_n)
      ha_pos ha_lt1 hθ_pos hθ_lt1 hLn_nn
    · -- Goal: Ln' ≤ (1-a) * Ln + (δ_curv + proj_err_n)
      rw [hLn'_eq, hLn_eq]
      linarith [h_Un1_half, h_flat]
    · -- Goal: (δ_curv + proj_err_n) ≤ θ * a * Ln
      exact h_absorb
  case x_next_in =>
    /- Uses shared hηL and hg_zero_mstar. -/
    rw [Metric.mem_ball]
    have hgrad_lip : ‖gn‖ ≤ (L : ℝ) * dist x'n m_star := by
      have h := hf_lip.dist_le_mul x'n (hΩp_sub_Up (hΩ_sub_Ωp hx'_in)) m_star hm_star_Up
      rwa [hg_zero_mstar, dist_zero_right] at h
    have h_sn1_x : sn1.x = x'n - η • gn := rfl
    have h_step_dist : dist sn1.x x'n = η * ‖gn‖ := by
      rw [h_sn1_x, dist_eq_norm]
      have : (x'n - η • gn) - x'n = -(η • gn) := by abel
      rw [this, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hη_pos]
    calc dist sn1.x m_star
        ≤ dist sn1.x x'n + dist x'n m_star := dist_triangle _ _ _
      _ = η * ‖gn‖ + dist x'n m_star := by rw [h_step_dist]
      _ ≤ η * ((L : ℝ) * dist x'n m_star) + dist x'n m_star := by
          linarith [mul_le_mul_of_nonneg_left hgrad_lip (le_of_lt hη_pos)]
      _ = 2 * dist x'n m_star := by
          have : η * ((L : ℝ) * dist x'n m_star) = dist x'n m_star := by
            rw [← mul_assoc, hηL, one_mul]
          linarith
      _ < 2 * r₀ / 3 := by linarith [hx'_ball_r09]
  case x'_next_in =>
    /- x'_{n+1} = (1+ρ)·x_{n+1} - ρ·x_n  (convex-like combination).
       Need: x'_{n+1} ∈ B(m⋆, 2r₀/3).
       By triangle inequality via this identity:
         dist(x'_{n+1}, m⋆) ≤ (1+ρ)·dist(x_{n+1}, m⋆) + ρ·dist(x_n, m⋆)
                            < (1+ρ)·2(r₀/9) + ρ·(r₀/9)
                            = (2+3ρ)/9 · r₀ < 5r₀/9 < 2r₀/3. -/
    rw [Metric.mem_ball]
    have hx_ball := Metric.mem_ball.mp hx_in
    have hx_ball_r09 : dist sn.x m_star < r₀ / 9 :=
      lt_of_lt_of_le hx_ball (min_le_left _ _)
    have hgrad_lip : ‖gn‖ ≤ (L : ℝ) * dist x'n m_star := by
      have h := hf_lip.dist_le_mul x'n (hΩp_sub_Up (hΩ_sub_Ωp hx'_in)) m_star hm_star_Up
      rwa [hg_zero_mstar, dist_zero_right] at h
    have hρ_lt1 : ρ < 1 := by
      rw [hρ]; rw [div_lt_one (by linarith : (0 : ℝ) < 1 + a)]; linarith
    -- Key identity: x'_{n+1} = (1+ρ)·x_{n+1} - ρ·x_n
    have h_conv : sn1.lookahead η = (1 + ρ) • sn1.x - ρ • sn.x := by
      change sn1.x + Real.sqrt η • sn1.v = (1 + ρ) • sn1.x - ρ • sn.x
      have hsq : Real.sqrt η * Real.sqrt η = η :=
        Real.mul_self_sqrt (le_of_lt hη_pos)
      have h5 : Real.sqrt η • (ρ • (sn.v - Real.sqrt η • gn)) =
          ρ • (Real.sqrt η • sn.v - η • gn) := by
        rw [smul_comm (Real.sqrt η) ρ, smul_sub, ← mul_smul, hsq]
      change (x'n - η • gn) + Real.sqrt η • (ρ • (sn.v - Real.sqrt η • gn)) =
        (1 + ρ) • (x'n - η • gn) - ρ • sn.x
      rw [h5]
      change (sn.x + Real.sqrt η • sn.v - η • gn) +
          ρ • (Real.sqrt η • sn.v - η • gn) =
        (1 + ρ) • (sn.x + Real.sqrt η • sn.v - η • gn) - ρ • sn.x
      module
    -- Distance bound on x_{n+1}: dist(x_{n+1}, m⋆) < 2·(r₀/9)
    have h_sn1_dist : dist sn1.x m_star < 2 * (r₀ / 9) := by
      have h_sn1_x : sn1.x = x'n - η • gn := rfl
      have h_step_dist : dist sn1.x x'n = η * ‖gn‖ := by
        rw [h_sn1_x, dist_eq_norm]
        have : (x'n - η • gn) - x'n = -(η • gn) := by abel
        rw [this, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hη_pos]
      calc dist sn1.x m_star
          ≤ dist sn1.x x'n + dist x'n m_star := dist_triangle _ _ _
        _ = η * ‖gn‖ + dist x'n m_star := by rw [h_step_dist]
        _ ≤ η * ((L : ℝ) * dist x'n m_star) + dist x'n m_star := by
            linarith [mul_le_mul_of_nonneg_left hgrad_lip (le_of_lt hη_pos)]
        _ = 2 * dist x'n m_star := by
            have : η * ((L : ℝ) * dist x'n m_star) = dist x'n m_star := by
              rw [← mul_assoc, hηL, one_mul]
            linarith
        _ < 2 * (r₀ / 9) := by linarith [hx'_ball_r09]
    -- Subtract m_star using the convex combination identity
    have h_sub : sn1.lookahead η - m_star =
        (1 + ρ) • (sn1.x - m_star) - ρ • (sn.x - m_star) := by
      rw [h_conv]; module
    -- Main distance bound via triangle inequality
    calc dist (sn1.lookahead η) m_star
        = ‖sn1.lookahead η - m_star‖ := dist_eq_norm _ _
      _ = ‖(1 + ρ) • (sn1.x - m_star) - ρ • (sn.x - m_star)‖ := by
          rw [h_sub]
      _ ≤ ‖(1 + ρ) • (sn1.x - m_star)‖ + ‖ρ • (sn.x - m_star)‖ :=
          norm_sub_le _ _
      _ = (1 + ρ) * ‖sn1.x - m_star‖ + ρ * ‖sn.x - m_star‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < 1 + ρ),
              Real.norm_eq_abs, abs_of_pos hρ_pos]
      _ = (1 + ρ) * dist sn1.x m_star + ρ * dist sn.x m_star := by
          simp only [dist_eq_norm]
      _ < (1 + ρ) * (2 * (r₀ / 9)) + ρ * (r₀ / 9) := by
          have h1 : (1 + ρ) * dist sn1.x m_star < (1 + ρ) * (2 * (r₀ / 9)) :=
            mul_lt_mul_of_pos_left h_sn1_dist (by linarith : (0:ℝ) < 1 + ρ)
          have h2 : ρ * dist sn.x m_star < ρ * (r₀ / 9) :=
            mul_lt_mul_of_pos_left hx_ball_r09 hρ_pos
          linarith
      _ = (2 + 3 * ρ) / 9 * r₀ := by ring
      _ < 2 / 3 * r₀ := by
          have hcoef : (2 + 3 * ρ) / 9 < (2 : ℝ) / 3 := by linarith
          exact mul_lt_mul_of_pos_right hcoef hr₀_pos
      _ = 2 * r₀ / 3 := by ring


/-- Public theorem wrapper for `lyapunovContractionProof`. -/
theorem lyapunov_contraction
    {d : ℕ} (_hd : 0 < d)
    -- The objective function
    (f : E d → ℝ)
    -- Parameters
    (L : ℝ≥0) (hL : 0 < (L : ℝ))
    (μ' : ℝ) (hμ' : 0 < μ')
    (θ : ℝ) (hθ_pos : 0 < θ) (hθ_lt1 : θ < 1)
    (η : ℝ) (hη : η = 1 / (L : ℝ)) (hη_pos : 0 < η)
    (ρ : ℝ) (hρ : ρ = (1 - Real.sqrt (μ' * η)) / (1 + Real.sqrt (μ' * η)))
    -- S = argmin set
    (S : Set (E d))
    (hM_argmin : S = argminSet f)
    -- Nearest-point projection
    (π : E d → E d)
    (_hπ_in_S : ∀ x, π x ∈ S)
    (_hπ_proj : ∀ x ∈ S, π x = x)
    -- Gradient vanishes on S
    (hgrad_zero : ∀ x ∈ S, gradient f x = 0)
    -- Tangent projector P = Dπ(m⋆)
    (P : E d →L[ℝ] E d)
    -- Base point
    (m_star : E d) (hm_star : m_star ∈ S)
    -- ε from `local_fiberwise_geometry`
    (ε : ℝ) (hε_pos : 0 < ε) (hε_bound : ε * η ≤ Real.sqrt (μ' * η))
    (hμη_lt1 : μ' * η < 1)
    -- Strong aiming on U₊ (from `local_fiberwise_geometry`)
    (U_plus : Set (E d))
    (hU_open : IsOpen U_plus)
    (hm_star_Up : m_star ∈ U_plus)
    -- Local smoothness on U₊
    (hf_diff_on : DifferentiableOn ℝ f U_plus)
    (hf_lip : LipschitzOnWith L (gradient f) U_plus)
    (hStrAim : ∀ x ∈ U_plus,
      @inner ℝ _ _ (gradient f x) (x - π x) ≥
        f x - fStar f + μ' / 2 * ‖x - π x‖ ^ 2)
    -- Hessian lower bound on U₊ (from `local_fiberwise_geometry`)
    (hHess_lower : ∀ x ∈ U_plus, ∀ ξ : E d,
      hessianQuadForm f x ξ ≥ -ε * ‖ξ‖ ^ 2)
    -- Normal Hessian on projection fibers: Dπ(π x) · e = 0 → e lies in normal space
    (_hπ_kills_normal : ∀ x ∈ U_plus,
      fderiv ℝ π (π x) (x - π x) = 0)
    -- P is self-adjoint (orthogonal projector property)
    (hP_self_adj : ∀ x y : E d, @inner ℝ _ _ (P x) y = @inner ℝ _ _ x (P y))
    -- P is idempotent (orthogonal projector property)
    (hP_idem : ∀ x : E d, P (P x) = P x)
    -- Segment estimate (from D²f ≽ -εI and C² regularity):
    --   ⟨∇f(x), x - z⟩ ≥ f(x) - f(z) - ε/2 · ‖x - z‖²
    (hSegment : ∀ x z : E d, x ∈ U_plus → z ∈ U_plus →
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 → (1 - t) • z + t • x ∈ U_plus) →
      @inner ℝ _ _ (gradient f x) (x - z) ≥
        f x - f z - ε / 2 * ‖x - z‖ ^ 2)
    -- Total perturbation absorption (curvature + projector-freezing error)
    -- δ_curv = curvature perturbation, proj_err = a·|⟨g, Pe⟩| from projector freezing
    -- R_abs is the energy/spatial radius: iterates must be in B(m⋆, R_abs) with Ln ≤ R_abs².
    (R_abs : ℝ) (hR_abs : 0 < R_abs)
    (h_curv_absorb : ∀ (x₁ : E d) (n : ℕ),
      (nesterovSeq f η ρ x₁ n).x ∈ Metric.ball m_star R_abs →
      (nesterovSeq f η ρ x₁ n).lookahead η ∈ Metric.ball m_star R_abs →
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
      let proj_err := a * |@inner ℝ _ _ gn (P en)|
      δ_curv + proj_err ≤ θ * a * Ln)
    :
    -- Conclusion: ∃ Ω, R (independent of starting point) such that contraction holds
    ∃ (Ω Ω_plus : Set (E d)) (R : ℝ),
      IsOpen Ω ∧ IsOpen Ω_plus ∧ 0 < R ∧
      m_star ∈ Ω ∧ Ω ⊆ Ω_plus ∧ Ω_plus ⊆ U_plus ∧
      -- For all starting points and iterations with the right preconditions
      ∀ (x₁ : E d) (n : ℕ),
        let s := nesterovSeq f η ρ x₁ n
        let s' := nesterovSeq f η ρ x₁ (n + 1)
        let Ln := lyapunov P μ' π f η ρ x₁ n
        let Ln' := lyapunov P μ' π f η ρ x₁ (n + 1)
        let a := Real.sqrt (μ' * η)
        s.x ∈ Ω → s.lookahead η ∈ Ω → Ln ≤ R ^ 2 →
        -- Contraction
        Ln' ≤ (1 - (1 - θ) * a) * Ln ∧
        -- Next iterates in Ω⁺
        s'.x ∈ Ω_plus ∧ s'.lookahead η ∈ Ω_plus := by
  exact lyapunovContractionProof (d := d) (_hd := _hd) (f := f) (L := L) (hL := hL) (μ' := μ')
    (hμ' := hμ') (θ := θ) (hθ_pos := hθ_pos) (hθ_lt1 := hθ_lt1) (η := η) (hη := hη)
    (hη_pos := hη_pos) (ρ := ρ) (hρ := hρ) (S := S) (hM_argmin := hM_argmin) (π := π)
    (_hπ_in_S := _hπ_in_S) (_hπ_proj := _hπ_proj) (hgrad_zero := hgrad_zero) (P := P)
    (m_star := m_star) (hm_star := hm_star) (ε := ε) (hε_pos := hε_pos) (hε_bound := hε_bound)
    (hμη_lt1 := hμη_lt1) (U_plus := U_plus) (hU_open := hU_open) (hm_star_Up := hm_star_Up)
    (hf_diff_on := hf_diff_on) (hf_lip := hf_lip) (hStrAim := hStrAim) (hHess_lower := hHess_lower)
    (_hπ_kills_normal := _hπ_kills_normal) (hP_self_adj := hP_self_adj) (hP_idem := hP_idem)
    (hSegment := hSegment) (R_abs := R_abs) (hR_abs := hR_abs) (h_curv_absorb := h_curv_absorb)

end PLAcceleratedNesterovLean
