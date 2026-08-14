/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import LeanPool.PLAcceleratedNesterovLean.Convergence.GenLocalArgument
import LeanPool.PLAcceleratedNesterovLean.Convergence.RateArithmetic

/-!
# Local Convergence Argument

The zero-velocity result in this file is a specialization of
`local_convergence_at_base_point_gen`.  The adapter below supplies the small
initial-energy neighborhood and converts the generalized state sequence back
to `nesterovSeq`.
-/

noncomputable section

namespace PLAcceleratedNesterovLean

open scoped Topology NNReal
open Manifold

/-- Local convergence at a single base point m⋆ ∈ M. -/
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
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let η := 1 / (L : ℝ)
  let ρ := (1 - Real.sqrt (μ_minus * η)) / (1 + Real.sqrt (μ_minus * η))
  let P := fderiv ℝ π mstar
  have hη_pos : 0 < η := by positivity
  obtain ⟨Ω, δ, r_ball, C_coer, hΩ_open, hmstar_Ω, hΩ_sub_U, hδ_pos,
      hr_ball_pos, hC_coer_pos, hball_Ω, _hP_idem, _hP_norm, hμη_lt1,
      hcoer, hgen⟩ :=
    local_convergence_at_base_point_gen hd L hL μ hμ hμ_le_L μ_minus hμ_minus
      hμ_minus_lt θ hθ hθ_lt1 f S hrange U hTub_sub hPL hf_C2 hf_lip π
      hπ_on_U hπ_fix hπ_in_S hgrad_zero mstar hmstar
  -- A zero-velocity state's initial Lyapunov value is continuous and vanishes
  -- at the minimizer, so a sufficiently small start ball meets the gen entry
  -- condition.
  have hmstar_argmin : mstar ∈ argminSet f := by rw [← hrange]; exact hmstar
  have hmin : ∀ y, f mstar ≤ f y := hmstar_argmin
  have hbdd : BddBelow (Set.range f) :=
    ⟨f mstar, by rintro _ ⟨x, rfl⟩; exact hmin x⟩
  have hπ_cont : ContinuousAt π mstar := by
    have hne : S.Nonempty := ⟨mstar, hmstar⟩
    have hcanonical := tubularProj_continuousAt_of_mem hTub_sub hne hmstar
    apply hcanonical.congr
    exact (hTub_sub.isOpen.eventually_mem (hTub_sub.subset hmstar)).mono fun x hx => by
      have ⟨hπS, hπdist⟩ := hπ_on_U x hx
      have ⟨hcanonicalS, hcanonicalDist⟩ := tubularProj_mem hTub_sub hne x hx
      exact ((hTub_sub.uniqueProj x hx).unique
        ⟨hcanonicalS, hcanonicalDist⟩ ⟨hπS, hπdist⟩)
  have hf_cont : ContinuousAt f mstar :=
    hf_C2.continuousOn.continuousAt (hTub_sub.isOpen.mem_nhds (hTub_sub.subset hmstar))
  have henergy_cont : ContinuousAt
      (fun x => (f x - fStar f) + μ_minus / 2 * ‖x - π x‖ ^ 2) mstar := by
    apply ContinuousAt.add
    · exact hf_cont.sub continuousAt_const
    · exact (ContinuousAt.mul continuousAt_const
        (ContinuousAt.pow (ContinuousAt.norm (continuousAt_id.sub hπ_cont)) 2))
  have henergy_zero :
      (f mstar - fStar f) + μ_minus / 2 * ‖mstar - π mstar‖ ^ 2 = 0 := by
    have hfstar : f mstar = fStar f :=
      le_antisymm (le_ciInf (fun x => hmin x)) (ciInf_le hbdd mstar)
    simp [hπ_fix mstar hmstar, hfstar]
  have hlyapunov_initial : ∀ x : E d,
      lyapunovOfState P μ_minus π f η ⟨x, 0⟩ =
        (f x - fStar f) + μ_minus / 2 * ‖x - π x‖ ^ 2 := by
    intro x
    unfold lyapunovOfState auxVarOfState normalDispOfState NesterovState.lookahead
    simp only [map_zero, sub_self, smul_zero, add_zero, zero_add, norm_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_right_inj]
    rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt hμ_minus.le]
    ring
  obtain ⟨α_energy, hα_energy_pos, hα_energy⟩ :
      ∃ α_energy : ℝ, 0 < α_energy ∧ ∀ x ∈ Metric.ball mstar α_energy,
        lyapunovOfState P μ_minus π f η ⟨x, 0⟩ ≤ δ ^ 2 := by
    have hδ_sq_pos : (0 : ℝ) < δ ^ 2 := by positivity
    rw [Metric.continuousAt_iff] at henergy_cont
    obtain ⟨α_energy, hα_energy_pos, hclose⟩ := henergy_cont (δ ^ 2) hδ_sq_pos
    refine ⟨α_energy, hα_energy_pos, fun x hx => ?_⟩
    have hxclose := hclose hx
    rw [Real.dist_eq, henergy_zero, sub_zero, abs_of_nonneg] at hxclose
    · rw [hlyapunov_initial]; linarith
    · have hnonneg := lyapunovOfState_nonneg P μ_minus π f η ⟨x, 0⟩
        hμ_minus hη_pos hμη_lt1 hbdd
      rwa [hlyapunov_initial] at hnonneg
  refine ⟨min (min δ r_ball) α_energy, by positivity, ?_, ?_⟩
  · intro x hx
    exact hΩ_sub_U (hball_Ω (Metric.ball_subset_ball
      (le_trans (min_le_left _ _) (min_le_right _ _)) hx))
  · intro x₁ hx₁
    let s₀ : NesterovState d := ⟨x₁, 0⟩
    have hx₁_δ : x₁ ∈ Metric.ball mstar δ :=
      Metric.ball_subset_ball
        (le_trans (min_le_left _ _) (min_le_left _ _)) hx₁
    have hlookahead₀ : s₀.lookahead η = x₁ := by simp [s₀, NesterovState.lookahead]
    have hentry_lookahead : s₀.lookahead η ∈ Metric.ball mstar δ := by
      rw [hlookahead₀]; exact hx₁_δ
    have hentry_energy : lyapunovOfState P μ_minus π f η s₀ ≤ δ ^ 2 := by
      exact hα_energy x₁ (Metric.ball_subset_ball (min_le_right _ _) hx₁)
    obtain ⟨hstay_Ω, _hstay_ball, hdecay, hfiber⟩ :=
      hgen s₀ hx₁_δ hentry_lookahead hentry_energy
    constructor
    · intro k
      simpa only [s₀, nesterovSeqGen_zero_vel] using hΩ_sub_U (hstay_Ω k).2
    · set r := 1 - (1 - θ) * Real.sqrt (μ_minus * η)
      set initialEnergy := lyapunovOfState P μ_minus π f η s₀
      have hsqrt_pos : 0 < Real.sqrt (μ_minus * η) :=
        Real.sqrt_pos_of_pos (mul_pos hμ_minus hη_pos)
      have hsqrt_lt_one : Real.sqrt (μ_minus * η) < 1 := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_lt_sqrt (mul_pos hμ_minus hη_pos).le hμη_lt1
      have hr_pos : 0 < r := by
        have : (1 - θ) * Real.sqrt (μ_minus * η) < 1 := by
          calc
            (1 - θ) * Real.sqrt (μ_minus * η) < 1 * Real.sqrt (μ_minus * η) := by
              exact mul_lt_mul_of_pos_right (by linarith) hsqrt_pos
            _ < 1 := by simpa using hsqrt_lt_one
        simp only [r]; linarith
      have hr_lt_one : r < 1 := by
        have : 0 < (1 - θ) * Real.sqrt (μ_minus * η) :=
          mul_pos (by linarith) hsqrt_pos
        simp only [r]; linarith
      have hinitial_nonneg : 0 ≤ initialEnergy :=
        lyapunovOfState_nonneg P μ_minus π f η s₀ hμ_minus hη_pos hμη_lt1 hbdd
      have hdecay_all : ∀ k : ℕ,
          lyapunovOfState P μ_minus π f η (nesterovSeqGen f η ρ s₀ k) ≤
            r ^ k * initialEnergy := by
        intro k
        cases k with
        | zero => simp [nesterovSeqGen, initialEnergy]
        | succ k => exact hdecay k
      -- Smoothness along the fiber and generalized coercivity control the
      -- function gap at every lookahead point by the current Lyapunov value.
      set C_gap := (L : ℝ) * C_coer / (2 * μ_minus)
      have hC_gap_pos : 0 < C_gap := by positivity
      have hgap_bound : ∀ k : ℕ,
          f ((nesterovSeqGen f η ρ s₀ k).lookahead η) - fStar f ≤
            C_gap * lyapunovOfState P μ_minus π f η
              (nesterovSeqGen f η ρ s₀ k) := by
        intro k
        let sk := nesterovSeqGen f η ρ s₀ k
        let y := sk.lookahead η
        let e := y - π y
        let energy := lyapunovOfState P μ_minus π f η sk
        have hyU : y ∈ U := hΩ_sub_U (hstay_Ω k).2
        have hπyS : π y ∈ S := (hπ_on_U y hyU).1
        have hπyU : π y ∈ U := hTub_sub.subset hπyS
        have hfπ : f (π y) = fStar f := by
          have hπmin : ∀ z, f (π y) ≤ f z := by
            have : π y ∈ argminSet f := by rw [← hrange]; exact hπyS
            exact this
          exact le_antisymm (le_ciInf hπmin) (ciInf_le hbdd (π y))
        have hsegment : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → π y + t • e ∈ U := by
          intro t ht0 ht1
          simpa only [sk, y, e] using hfiber k t ht0 ht1
        have hqub : f (π y + e) - f (π y) ≤
            @inner ℝ _ _ (gradient f (π y)) e + (L : ℝ) / 2 * ‖e‖ ^ 2 :=
          lsmooth_qub f L hTub_sub.isOpen (hf_C2.differentiableOn two_ne_zero)
            hf_lip (π y) e hπyU hsegment
        have hπe : π y + e = y := by simp only [e]; abel
        have hgradπ : gradient f (π y) = 0 := hgrad_zero (π y) hπyS
        rw [hπe, hfπ, hgradπ, inner_zero_left, zero_add] at hqub
        have hcoer_pair := hcoer sk (hstay_Ω k).1 (hstay_Ω k).2
        have he_sq : μ_minus * ‖e‖ ^ 2 ≤ C_coer * energy := by
          simp only [normalDispOfState, y, e, energy] at hcoer_pair ⊢
          linarith [sq_nonneg ‖sk.v‖]
        have hkey : μ_minus * (f y - fStar f) ≤
            (L : ℝ) / 2 * C_coer * energy := by
          calc
            μ_minus * (f y - fStar f)
                ≤ μ_minus * ((L : ℝ) / 2 * ‖e‖ ^ 2) :=
                  mul_le_mul_of_nonneg_left hqub hμ_minus.le
            _ = (L : ℝ) / 2 * (μ_minus * ‖e‖ ^ 2) := by ring
            _ ≤ (L : ℝ) / 2 * (C_coer * energy) :=
              mul_le_mul_of_nonneg_left he_sq (by positivity)
            _ = (L : ℝ) / 2 * C_coer * energy := by ring
        change f y - fStar f ≤ C_gap * energy
        simp only [C_gap]
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * μ_minus)).mpr
        nlinarith
      have htarget_pos : 0 < (1 - θ) ^ 2 * μ_minus := by positivity
      have hsqrt_target_pos : 0 < Real.sqrt ((L : ℝ) / ((1 - θ) ^ 2 * μ_minus)) :=
        Real.sqrt_pos_of_pos (div_pos hL htarget_pos)
      have hrate : r ≤ Real.exp
          (-(1 / Real.sqrt ((L : ℝ) / ((1 - θ) ^ 2 * μ_minus)))) := by
        let b := (1 - θ) * Real.sqrt (μ_minus * η)
        have hb_nonneg : 0 ≤ b := by positivity
        have hratio_nonneg : 0 ≤ (L : ℝ) / ((1 - θ) ^ 2 * μ_minus) := by positivity
        have hproduct :
            b * Real.sqrt ((L : ℝ) / ((1 - θ) ^ 2 * μ_minus)) = 1 := by
          have hsqrt_mul := Real.sqrt_mul (sq_nonneg b)
            ((L : ℝ) / ((1 - θ) ^ 2 * μ_minus))
          rw [Real.sqrt_sq hb_nonneg] at hsqrt_mul
          rw [hsqrt_mul.symm]
          have hb_sq : b ^ 2 = (1 - θ) ^ 2 * (μ_minus * η) := by
            simp only [b, mul_pow, Real.sq_sqrt (mul_pos hμ_minus hη_pos).le]
          rw [hb_sq]
          have : (1 - θ) ^ 2 * (μ_minus * η) *
              ((L : ℝ) / ((1 - θ) ^ 2 * μ_minus)) = 1 := by
            simp only [η]
            field_simp [ne_of_gt hL, ne_of_gt hμ_minus,
              ne_of_gt (sub_pos.mpr hθ_lt1)]
          rw [this, Real.sqrt_one]
        have hb_eq : b = 1 / Real.sqrt ((L : ℝ) / ((1 - θ) ^ 2 * μ_minus)) := by
          rw [eq_div_iff (ne_of_gt hsqrt_target_pos)]
          exact hproduct
        simpa only [r, b, hb_eq] using
          Real.one_sub_le_exp_neg (1 / Real.sqrt ((L : ℝ) / ((1 - θ) ^ 2 * μ_minus)))
      have hbound : ∀ k : ℕ,
          f ((nesterovSeqGen f η ρ s₀ k).lookahead η) - fStar f ≤
            (C_gap * initialEnergy + 1) * r ^ k := by
        intro k
        calc
          f ((nesterovSeqGen f η ρ s₀ k).lookahead η) - fStar f
              ≤ C_gap * lyapunovOfState P μ_minus π f η
                  (nesterovSeqGen f η ρ s₀ k) := hgap_bound k
          _ ≤ C_gap * (r ^ k * initialEnergy) :=
            mul_le_mul_of_nonneg_left (hdecay_all k) hC_gap_pos.le
          _ = (C_gap * initialEnergy) * r ^ k := by ring
          _ ≤ (C_gap * initialEnergy + 1) * r ^ k :=
            mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hr_pos.le k)
      have hrate_gen := hasAcceleratedRate_of_geometric_decay f
        (fun k => (nesterovSeqGen f η ρ s₀ k).lookahead η)
        (L : ℝ) ((1 - θ) ^ 2 * μ_minus) (C_gap * initialEnergy + 1) r
        (by positivity) hr_pos hr_lt_one hrate hbound
      simpa only [s₀, nesterovSeqGen_zero_vel] using hrate_gen

end PLAcceleratedNesterovLean
