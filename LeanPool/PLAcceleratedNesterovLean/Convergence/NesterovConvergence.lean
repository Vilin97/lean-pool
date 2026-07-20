/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import LeanPool.PLAcceleratedNesterovLean.Convergence.GenLocalArgument
import LeanPool.PLAcceleratedNesterovLean.Convergence.RateArithmetic
import LeanPool.PLAcceleratedNesterovLean.Convergence.PhaseSchedule
import LeanPool.PLAcceleratedNesterovLean.Convergence.Coercivity.Step1
import LeanPool.PLAcceleratedNesterovLean.Convergence.LyapunovContraction.Step1

/-!
# Retuned Nesterov Convergence

The Nesterov algorithm achieves the sharp PL exponent by running with an
internal parameter just below μ.

## Key scalar comparison

The general local theorem gives per-step Lyapunov contraction rate
  r = 1 − (1−θ)·√(μ'·η).
The main specialization sets μ' = μ·(1−θ), η = 1/L, and chooses
`0 < θ ≤ √(μ/L)/8`.

## Local theorem variants

* `nesterov_convergence_at_base_point_position_params`:
  state positions `xₖ`; arbitrary `μ'`, `θ`, `ρ`, plus a scalar rate bound;
  reusable core theorem.
* `nesterov_convergence_at_base_point_position_theta`:
  state positions `xₖ`; explicit retuning parameter `θ`, `ρ = rhoOfTheta`;
  local specialized theorem.
-/

noncomputable section

namespace PLAcceleratedNesterovLean

open scoped Topology NNReal
open Manifold


variable {d : ℕ}

/-! ## Rate bound: r ≤ exp(-√(μ/L)) -/

/-- For θ ≤ a/8 and 0 < a ≤ 2: 1 − (1−2θ)a ≤ exp(−a). -/
private lemma rate_bound_case_small {θ a : ℝ}
    (hθ_nn : 0 ≤ θ) (hθ_le : θ ≤ a / 8)
    (_ha_pos : 0 < a) (ha_le2 : a ≤ 2) :
    1 - (1 - 2 * θ) * a ≤ Real.exp (-a) := by
  have h_exp_lb : 1 - a + a ^ 2 / 4 ≤ Real.exp (-a) := by
    have h := @Real.one_sub_div_pow_le_exp_neg 2 a (by simp; linarith : a ≤ ↑(2 : ℕ))
    simp only [Nat.cast_ofNat] at h
    nlinarith [sq_nonneg (1 - a / 2)]
  nlinarith

/-- For θ ≤ 1/4 and a ≥ 2: (1−θ)√(1−θ) ≥ 1/2, so rate ≤ 1−a/2 ≤ 0 ≤ exp(−a). -/
private lemma rate_bound_case_large {θ a : ℝ}
    (_hθ_nn : 0 ≤ θ) (hθ_le : θ ≤ 1 / 4)
    (ha_ge2 : 2 ≤ a) :
    1 - (1 - θ) * Real.sqrt (1 - θ) * a ≤ Real.exp (-a) := by
  have h1θ_nn : (0 : ℝ) ≤ 1 - θ := by linarith
  have h1θ_ge : (3 : ℝ)/4 ≤ 1 - θ := by linarith
  have h_sqrt_lb : Real.sqrt (1 - θ) ≥ 2/3 := by
    rw [ge_iff_le, ← Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2/3)]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (2:ℝ)])
  have h_prod : (1 - θ) * Real.sqrt (1 - θ) ≥ 1/2 := by nlinarith
  have h1 : (1 - θ) * Real.sqrt (1 - θ) * a ≥ 1 := by nlinarith
  linarith [Real.exp_pos (-a)]

-- Scalar comparison with the retuning parameter θ explicit.
/-- If `0 < θ ≤ min (√(μ/L)/8) (1/4)`, then the retuned one-step factor from
the theorem statement is bounded by the sharp exponential `exp(-√(μ/L))`. -/
theorem nesterov_rate_bound_theta
    (L : ℝ≥0) (hL : 0 < (L : ℝ))
    (μ : ℝ) (hμ : 0 < μ)
    (θ : ℝ) (hθ_pos : 0 < θ)
    (hθ_le : θ ≤ Real.sqrt (μ / ↑L) / 8)
    (hθ_le_quarter : θ ≤ 1 / 4) :
    1 - (1 - θ) * Real.sqrt (muOfTheta μ θ * (1 / ↑L)) ≤
      Real.exp (-(1 / Real.sqrt (↑L / μ))) := by
  set a := Real.sqrt (μ / ↑L) with ha_def
  have h1θ_nn : 0 ≤ 1 - θ := by linarith
  have ha_pos : 0 < a := Real.sqrt_pos_of_pos (div_pos hμ hL)
  have h_prod_eq : muOfTheta μ θ * (1 / ↑L) = (μ / ↑L) * (1 - θ) := by
    change μ * (1 - θ) * (1 / ↑L) = μ / ↑L * (1 - θ)
    ring
  rw [h_prod_eq, Real.sqrt_mul (div_pos hμ hL).le]
  have h_target_eq : -(1 / Real.sqrt (↑L / μ)) = -a := by
    rw [ha_def, one_div, ← Real.sqrt_inv, inv_div]
  rw [h_target_eq]
  have h_sqrt_lb : Real.sqrt (1 - θ) ≥ 1 - θ := by
    have hle : (1 - θ) ^ 2 ≤ 1 - θ := by nlinarith [mul_nonneg hθ_pos.le h1θ_nn]
    calc (1 : ℝ) - θ = Real.sqrt ((1 - θ) ^ 2) := (Real.sqrt_sq h1θ_nn).symm
      _ ≤ Real.sqrt (1 - θ) := Real.sqrt_le_sqrt hle
  have h_prod_lb : (1 - θ) * Real.sqrt (1 - θ) ≥ 1 - 2 * θ := by
    nlinarith [mul_le_mul_of_nonneg_left h_sqrt_lb h1θ_nn, sq_nonneg θ]
  have h_rate_ub : 1 - (1 - θ) * (a * Real.sqrt (1 - θ)) ≤
      1 - (1 - 2 * θ) * a := by
    have : (1 - θ) * (a * Real.sqrt (1 - θ)) =
        (1 - θ) * Real.sqrt (1 - θ) * a := by ring
    rw [this]; nlinarith
  by_cases ha2 : a ≤ 2
  · linarith [rate_bound_case_small hθ_pos.le hθ_le ha_pos ha2]
  · push Not at ha2
    linarith [rate_bound_case_large hθ_pos.le hθ_le_quarter ha2.le]

-- The local assembly uses the full Lyapunov argument and rate conversion.
/-! ## State-position local theorem family -/

/-- Parameterized local convergence theorem for the base positions `xₙ`.

The update queries the gradient at the look-ahead point
`xₙ' = xₙ + √η vₙ`, but the theorem states the rate for the state positions
`xₙ`.  The retuned internal parameter `μ'`, absorption budget `θ`, and momentum
`ρ` are all explicit. -/
theorem nesterov_convergence_at_base_point_position_params
    {d : ℕ} (hd : 0 < d)
    (L : ℝ≥0) (hL : 0 < (L : ℝ))
    (μ : ℝ) (hμ : 0 < μ) (hμ_le_L : μ ≤ ↑L)
    (μ' : ℝ) (hμ'_pos : 0 < μ') (hμ'_lt : μ' < μ)
    (θ : ℝ) (hθ_pos : 0 < θ) (hθ_lt1 : θ < 1)
    (ρ : ℝ)
    (hρ : ρ = (1 - Real.sqrt (μ' * (1 / ↑L))) /
      (1 + Real.sqrt (μ' * (1 / ↑L))))
    (hrate : 1 - (1 - θ) * Real.sqrt (μ' * (1 / ↑L)) ≤
      Real.exp (-(1 / Real.sqrt (↑L / μ))))
    (f : E d → ℝ) (S : Set (E d)) (hrange : S = argminSet f)
    (U : Set (E d))
    (hTub : IsTubularNeighborhoodOfSubmanifold S U)
    (hPL : PolyakLojasiewicz f μ U)
    (hC2 : ContDiffOn ℝ 2 f U)
    (hLip : LipschitzOnWith ↑L (gradient f) U)
    (π : E d → E d)
    (hπ_on_U : ∀ x ∈ U, π x ∈ S ∧ dist x (π x) = Metric.infDist x S)
    (hπ_fix : ∀ x ∈ S, π x = x)
    (hπ_in_S : ∀ x, π x ∈ S)
    (hgrad_zero : ∀ x ∈ S, gradient f x = 0)
    (mstar : E d) (hmstar : mstar ∈ S) :
    ∃ (α : ℝ), 0 < α ∧
      Metric.ball mstar α ⊆ U ∧
      ∀ x₀ ∈ Metric.ball mstar α,
        (∀ k,
          (nesterovSeqGen f (1 / ↑L) ρ ⟨x₀, 0⟩ k).x ∈ U ∧
          (nesterovSeqGen f (1 / ↑L) ρ ⟨x₀, 0⟩ k).lookahead
            (1 / ↑L) ∈ U) ∧
        HasAcceleratedRateWithPrefactorTwo f
          (fun k => (nesterovSeqGen f (1 / ↑L) ρ ⟨x₀, 0⟩ k).x)
          ↑L μ x₀ ∧
        HasAcceleratedRate f
          (fun k => (nesterovSeqGen f (1 / ↑L) ρ ⟨x₀, 0⟩ k).x)
          ↑L μ := by
  set η := 1 / (L : ℝ) with hη_def
  set P := fderiv ℝ π mstar with hP_def
  have hη_pos : 0 < η := by positivity
  obtain ⟨Ω, δ, r_ball, C_coer, hΩ_open, hm_Ω, hΩ_sub, hδ, hr_ball, hC_coer,
    hball_Ω, _hP_idem, _hP_norm, hμη_lt1, _hcoer, hgen⟩ :=
    local_convergence_at_base_point_gen hd L hL μ hμ hμ_le_L μ' hμ'_pos hμ'_lt
      θ hθ_pos hθ_lt1 f S hrange U hTub hPL hC2 hLip π hπ_on_U hπ_fix hπ_in_S
      hgrad_zero mstar hmstar
  have hρ_eq_gen : (1 - Real.sqrt (μ' * (1 / ↑L))) /
      (1 + Real.sqrt (μ' * (1 / ↑L))) = ρ := by
    exact hρ.symm
  simp only [hρ_eq_gen] at hgen
  set r := 1 - (1 - θ) * Real.sqrt (μ' * η) with hr_def
  have hμη_le1 : Real.sqrt (μ' * η) ≤ 1 := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (le_of_lt hμη_lt1)
  obtain ⟨U_qg, ε_qg, hU_qg_open, hm_U_qg, _hU_qg_cpt, hU_qg_sub,
      _hU_qg_convex, _hε_qg_pos, _hε_qg_le, _hNormHess_qg, hQG_qg,
      _hStrAim_qg, _hHessLow_qg, _hNormHess_mu_qg, _hseg_qg⟩ :=
    local_fiberwise_geometry hd f L hL μ hμ μ' hμ'_pos
      hμ'_lt η rfl hη_pos S hrange U hTub hPL hC2 π
      hπ_on_U hgrad_zero mstar hmstar
  obtain ⟨α_qg, hα_qg_pos, hball_qg⟩ :=
    Metric.isOpen_iff.mp hU_qg_open mstar hm_U_qg
  -- The initial Lyapunov value is continuous and vanishes at the minimizer.
  have hmstar_argmin : mstar ∈ argminSet f := by rw [← hrange]; exact hmstar
  have hmin : ∀ y, f mstar ≤ f y := hmstar_argmin
  have hbdd : BddBelow (Set.range f) :=
    ⟨f mstar, by rintro _ ⟨x, rfl⟩; exact hmin x⟩
  have hπ_cont : ContinuousAt π mstar := by
    have hne : S.Nonempty := ⟨mstar, hmstar⟩
    have hπ₀_cont := tubularProj_continuousAt_of_mem hTub hne hmstar
    apply hπ₀_cont.congr
    exact (hTub.isOpen.eventually_mem (hTub.subset hmstar)).mono fun x hx => by
      have ⟨h1, h2⟩ := hπ_on_U x hx
      have ⟨h3, h4⟩ := tubularProj_mem hTub hne x hx
      exact ((hTub.uniqueProj x hx).unique ⟨h3, h4⟩ ⟨h1, h2⟩)
  have hU_open := hTub.isOpen
  have hm_U : mstar ∈ U := hTub.subset hmstar
  have hf_cont : ContinuousAt f mstar :=
    (hC2.continuousOn.continuousAt (hU_open.mem_nhds hm_U))
  have hψ_cont : ContinuousAt
      (fun x => (f x - fStar f) + μ' / 2 * ‖x - π x‖ ^ 2) mstar := by
    apply ContinuousAt.add
    · exact hf_cont.sub continuousAt_const
    · apply ContinuousAt.mul continuousAt_const
      exact (ContinuousAt.pow (ContinuousAt.norm (continuousAt_id.sub hπ_cont)) 2)
  have hψ_zero : (f mstar - fStar f) + μ' / 2 * ‖mstar - π mstar‖ ^ 2 = 0 := by
    have h1 : f mstar = fStar f :=
      le_antisymm (le_ciInf (fun x => hmin x)) (ciInf_le hbdd mstar)
    simp_all
  have hlyap_eq_psi : ∀ x₀ : E d,
      lyapunovOfState P μ' π f η ⟨x₀, 0⟩ =
        (f x₀ - fStar f) + μ' / 2 * ‖x₀ - π x₀‖ ^ 2 := by
    intro x₀
    unfold lyapunovOfState auxVarOfState normalDispOfState NesterovState.lookahead
    simp only [map_zero, sub_self, smul_zero, add_zero, zero_add, norm_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_right_inj]
    rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt hμ'_pos.le]
    ring
  have hψ_small : ∃ α_ψ : ℝ, 0 < α_ψ ∧
      ∀ x₀ ∈ Metric.ball mstar α_ψ,
        lyapunovOfState P μ' π f η ⟨x₀, 0⟩ ≤ δ ^ 2 := by
    have hδ_sq_pos : (0 : ℝ) < δ ^ 2 := by positivity
    rw [Metric.continuousAt_iff] at hψ_cont
    obtain ⟨α_ψ, hα_ψ_pos, hα_ψ⟩ := hψ_cont (δ ^ 2) hδ_sq_pos
    refine ⟨α_ψ, hα_ψ_pos, fun x₀ hx₀ => ?_⟩
    have h := hα_ψ hx₀
    rw [Real.dist_eq, hψ_zero, sub_zero, abs_of_nonneg] at h
    · rw [hlyap_eq_psi]; linarith
    · have hnn := lyapunovOfState_nonneg P μ' π f η ⟨x₀, 0⟩ hμ'_pos hη_pos hμη_lt1 hbdd
      rw [hlyap_eq_psi] at hnn; exact hnn
  obtain ⟨α_ψ, hα_ψ_pos, hα_ψ_bound⟩ := hψ_small
  -- Shrink the start ball to satisfy the gen theorem's spatial and energy entries.
  refine ⟨min (min (min δ r_ball) α_ψ) α_qg, by positivity, ?_, ?_⟩
  · intro x hx
    exact hΩ_sub (hball_Ω (Metric.ball_subset_ball
      (le_trans (min_le_left _ _)
        (le_trans (min_le_left _ _) (min_le_right _ _))) hx))
  · intro x₀ hx₀
    set s₀ : NesterovState d := ⟨x₀, 0⟩ with hs₀_def
    have hx₀_δ : x₀ ∈ Metric.ball mstar δ :=
      Metric.ball_subset_ball
        (le_trans (min_le_left _ _)
          (le_trans (min_le_left _ _) (min_le_left _ _))) hx₀
    have h_la0 : s₀.lookahead η = x₀ := by
      change x₀ + Real.sqrt η • (0 : E d) = x₀; simp
    have h_entry_la : s₀.lookahead η ∈ Metric.ball mstar δ := by rw [h_la0]; exact hx₀_δ
    have h_entry_lyap : lyapunovOfState P μ' π f η s₀ ≤ δ ^ 2 :=
      hα_ψ_bound x₀ (Metric.ball_subset_ball
        (le_trans (min_le_left _ _) (min_le_right _ _)) hx₀)
    have hx₀_qg : x₀ ∈ U_qg :=
      hball_qg (Metric.ball_subset_ball (min_le_right _ _) hx₀)
    have hx₀_U : x₀ ∈ U := hU_qg_sub (subset_closure hx₀_qg)
    obtain ⟨h_in_Ω, _h_in_ball, h_lyap_decay, _h_fiber_seg⟩ :=
      hgen s₀ hx₀_δ h_entry_la h_entry_lyap
    refine ⟨fun k => ⟨hΩ_sub (h_in_Ω k).1, hΩ_sub (h_in_Ω k).2⟩, ?_⟩
    -- The Lyapunov function contains the base-position gap directly.
    set L₀ := lyapunovOfState P μ' π f η s₀
    have hL₀_nn : 0 ≤ L₀ := lyapunovOfState_nonneg P μ' π f η s₀
      hμ'_pos hη_pos hμη_lt1 hbdd
    have hgap₀_nn : 0 ≤ f x₀ - fStar f := by
      exact sub_nonneg.mpr (ciInf_le hbdd x₀)
    have hQG₀_norm : f x₀ - fStar f ≥ μ' / 2 * ‖x₀ - π x₀‖ ^ 2 := by
      have hQG₀ := hQG_qg x₀ hx₀_qg
      have hdist := (hπ_on_U x₀ hx₀_U).2
      rw [← hdist, dist_eq_norm] at hQG₀
      exact hQG₀
    have hL₀_le_two_gap : L₀ ≤ 2 * (f x₀ - fStar f) := by
      rw [show L₀ = (f x₀ - fStar f) + μ' / 2 * ‖x₀ - π x₀‖ ^ 2 from
        (hlyap_eq_psi x₀)]
      nlinarith
    have hsqrt_pos : 0 < Real.sqrt (μ' * η) := Real.sqrt_pos_of_pos (by positivity)
    have hr_pos : 0 < r := by
      simp only [hr_def]
      have h1 : (1 - θ) * Real.sqrt (μ' * η) < 1 := by
        calc (1 - θ) * Real.sqrt (μ' * η)
            ≤ (1 - θ) * 1 := by
              apply mul_le_mul_of_nonneg_left hμη_le1 (by linarith)
          _ = 1 - θ := mul_one _
          _ < 1 := by linarith
      linarith
    have hr_lt1 : r < 1 := by
      simp only [hr_def]; linarith [mul_pos (by linarith : 0 < 1 - θ) hsqrt_pos]
    have h_lyap_all : ∀ k : ℕ,
        lyapunovOfState P μ' π f η (nesterovSeqGen f η ρ s₀ k) ≤ r ^ k * L₀ := by
      intro k; cases k with
      | zero =>
        change lyapunovOfState P μ' π f η s₀ ≤ 1 * L₀
        have : L₀ = lyapunovOfState P μ' π f η s₀ := rfl
        linarith
      | succ j => exact h_lyap_decay j
    have h_bound : ∀ k : ℕ,
        f (nesterovSeqGen f η ρ s₀ k).x - fStar f ≤ (L₀ + 1) * r ^ k := by
      intro k
      calc f (nesterovSeqGen f η ρ s₀ k).x - fStar f
          ≤ lyapunovOfState P μ' π f η (nesterovSeqGen f η ρ s₀ k) :=
            gap_le_lyapunovOfState_of_sqrt_le P μ' π f η
              (nesterovSeqGen f η ρ s₀ k) hμη_le1
        _ ≤ r ^ k * L₀ := h_lyap_all k
        _ = L₀ * r ^ k := by ring
        _ ≤ (L₀ + 1) * r ^ k := by
          exact mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hr_pos.le k)
    have hr_le_exp : r ≤ Real.exp (-(1 / Real.sqrt (↑L / μ))) := by
      simpa only [hr_def, hη_def] using hrate
    constructor
    · intro k
      have h_exp_pow :
          (Real.exp (-(1 / Real.sqrt (↑L / μ)))) ^ k =
            Real.exp (-(↑k / Real.sqrt (↑L / μ))) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring_nf
      calc f (nesterovSeqGen f (1 / ↑L) ρ ⟨x₀, 0⟩ k).x - fStar f
          = f (nesterovSeqGen f η ρ s₀ k).x - fStar f := by
              simp only [hη_def, hs₀_def]
        _ ≤ lyapunovOfState P μ' π f η (nesterovSeqGen f η ρ s₀ k) :=
            gap_le_lyapunovOfState_of_sqrt_le P μ' π f η
              (nesterovSeqGen f η ρ s₀ k) hμη_le1
        _ ≤ r ^ k * L₀ := h_lyap_all k
        _ ≤ r ^ k * (2 * (f x₀ - fStar f)) :=
            mul_le_mul_of_nonneg_left hL₀_le_two_gap (pow_nonneg hr_pos.le k)
        _ = (2 * (f x₀ - fStar f)) * r ^ k := by ring
        _ ≤ (2 * (f x₀ - fStar f)) *
              (Real.exp (-(1 / Real.sqrt (↑L / μ)))) ^ k := by
            apply mul_le_mul_of_nonneg_left
            · exact pow_le_pow_left₀ (le_of_lt hr_pos) hr_le_exp k
            · nlinarith
        _ = 2 * Real.exp (-(↑k / Real.sqrt (↑L / μ))) * (f x₀ - fStar f) := by
            rw [h_exp_pow]
            ring
    · have hseq_eq :
          (fun k => (nesterovSeqGen f (1 / ↑L) ρ ⟨x₀, 0⟩ k).x) =
            fun k => (nesterovSeqGen f η ρ s₀ k).x := by
        simp_all
      rw [hseq_eq]
      exact hasAcceleratedRate_of_geometric_decay f _ ↑L μ (L₀ + 1) r
        (by linarith) hr_pos hr_lt1 hr_le_exp h_bound

/-- Local convergence theorem for the base positions `xₙ` with explicit `θ`.

The extra formal assumption `θ ≤ 1/4` follows from `μ ≤ L` and
`θ ≤ √(μ/L)/8` in the public theorem; keeping it explicit here isolates the
scalar rate comparison from the local geometry proof. -/
theorem nesterov_convergence_at_base_point_position_theta
    {d : ℕ} (hd : 0 < d)
    (L : ℝ≥0) (hL : 0 < (L : ℝ))
    (μ : ℝ) (hμ : 0 < μ) (hμ_le_L : μ ≤ ↑L)
    (θ : ℝ) (hθ_pos : 0 < θ) (hθ_lt1 : θ < 1)
    (hθ_le : θ ≤ Real.sqrt (μ / ↑L) / 8)
    (hθ_le_quarter : θ ≤ 1 / 4)
    (f : E d → ℝ) (S : Set (E d)) (hrange : S = argminSet f)
    (U : Set (E d))
    (hTub : IsTubularNeighborhoodOfSubmanifold S U)
    (hPL : PolyakLojasiewicz f μ U)
    (hC2 : ContDiffOn ℝ 2 f U)
    (hLip : LipschitzOnWith ↑L (gradient f) U)
    (π : E d → E d)
    (hπ_on_U : ∀ x ∈ U, π x ∈ S ∧ dist x (π x) = Metric.infDist x S)
    (hπ_fix : ∀ x ∈ S, π x = x)
    (hπ_in_S : ∀ x, π x ∈ S)
    (hgrad_zero : ∀ x ∈ S, gradient f x = 0)
    (mstar : E d) (hmstar : mstar ∈ S) :
    ∃ (α : ℝ), 0 < α ∧
      Metric.ball mstar α ⊆ U ∧
      ∀ x₀ ∈ Metric.ball mstar α,
        (∀ k,
          (nesterovSeqGen f (1 / ↑L) (rhoOfTheta ↑L μ θ) ⟨x₀, 0⟩ k).x ∈ U ∧
          (nesterovSeqGen f (1 / ↑L) (rhoOfTheta ↑L μ θ) ⟨x₀, 0⟩ k).lookahead
            (1 / ↑L) ∈ U) ∧
        HasAcceleratedRateWithPrefactorTwo f
          (fun k => (nesterovSeqGen f (1 / ↑L) (rhoOfTheta ↑L μ θ) ⟨x₀, 0⟩ k).x)
          ↑L μ x₀ ∧
        HasAcceleratedRate f
          (fun k => (nesterovSeqGen f (1 / ↑L) (rhoOfTheta ↑L μ θ) ⟨x₀, 0⟩ k).x)
          ↑L μ := by
  refine nesterov_convergence_at_base_point_position_params hd L hL μ hμ hμ_le_L
    (muOfTheta μ θ) (muOfTheta_pos hμ hθ_lt1) (muOfTheta_lt_mu hμ hθ_pos)
    θ hθ_pos hθ_lt1 (rhoOfTheta ↑L μ θ) ?_ ?_ f S hrange U hTub hPL hC2 hLip π
    hπ_on_U hπ_fix hπ_in_S hgrad_zero mstar hmstar
  · rfl
  · exact nesterov_rate_bound_theta L hL μ hμ θ hθ_pos hθ_le hθ_le_quarter

end PLAcceleratedNesterovLean
