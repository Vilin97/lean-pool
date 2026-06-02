/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.GeneralizedResidueTheory.PVInfrastructure.UniformStepBound
import LeanPool.LeanModularForms.GeneralizedResidueTheory.Residue

/-!
# On-Curve Principal Value: General Infrastructure

General PV convergence machinery for piecewise C¹ curves: dyadic PV limits,
measurability of cutout integrands, arc angle injectivity, CPV avoidance
and concatenation lemmas. These results work for arbitrary curves and functions.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

attribute [local instance] Classical.propDecidable

noncomputable section

lemma pv_limit_via_dyadic {γ : ℝ → ℂ} {a b t₀ : ℝ} {L : ℂ}
    (hat₀ : t₀ ∈ Set.Ioo a b) (hL : L ≠ 0)
    (hγ_C2 : ContDiffAt ℝ 2 γ t₀) (hγ_deriv : deriv γ t₀ = L)
    (hγ_cont_deriv : ContinuousOn (deriv γ) (Set.Icc a b))
    (hγ_meas : Measurable γ)
    (hγ_cont : ContinuousOn γ (Set.Icc a b))
    (h_inj : ∀ t ∈ Set.Icc a b, γ t = γ t₀ → t = t₀) :
    ∃ limit : ℂ, Tendsto (fun ε =>
      ∫ t in a..b, if ε < ‖γ t - γ t₀‖ then (γ t - γ t₀)⁻¹ * deriv γ t else 0)
      (𝓝[>] 0) (𝓝 limit) := by
  have hab : a < b := lt_trans (Set.mem_Ioo.mp hat₀).1 (Set.mem_Ioo.mp hat₀).2
  obtain ⟨K, hK_pos, δ_P1, hδ_P1_pos, h_step_uniform⟩ :=
    pv_step_bound_ratio_two_uniform hab hat₀ hγ_C2 hγ_deriv hL
      hγ_meas hγ_cont_deriv hγ_cont h_inj
  let δ := δ_P1 / 2
  have hδ_pos : 0 < δ := by positivity
  have h_dyadic_lt : ∀ n : ℕ, δ / 2 ^ n < δ_P1 := fun n =>
    calc δ / 2 ^ n ≤ δ := div_le_self hδ_pos.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
      _ < δ_P1 := by simp only [δ]; linarith
  let I : ℝ → ℂ := fun ε => ∫ t in a..b,
    if ε < ‖γ t - γ t₀‖ then (γ t - γ t₀)⁻¹ * deriv γ t else 0
  have h_step : ∀ n, ‖I (δ / 2 ^ (n + 1)) - I (δ / 2 ^ n)‖ ≤ K * δ / 2 ^ n := fun n => by
    have hε₂_pos : 0 < δ / 2 ^ (n + 1) := div_pos hδ_pos (by positivity)
    have h_le : δ / 2 ^ (n + 1) ≤ δ / 2 ^ n :=
      div_le_div_of_nonneg_left hδ_pos.le (by positivity)
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_succ n))
    have h_ratio : δ / 2 ^ n ≤ 2 * (δ / 2 ^ (n + 1)) := by rw [pow_succ]; ring_nf; linarith
    have h_bound := h_step_uniform (δ / 2 ^ n) (δ / 2 ^ (n + 1)) hε₂_pos h_le h_ratio
      (h_dyadic_lt n)
    calc ‖I (δ / 2 ^ (n + 1)) - I (δ / 2 ^ n)‖
        ≤ K * (δ / 2 ^ n) := h_bound
      _ = K * δ / 2 ^ n := by ring
  have h_cauchy_seq : CauchySeq (fun n => I (δ / 2 ^ n)) :=
    cauchySeq_pv_dyadic hδ_pos hK_pos h_step
  obtain ⟨limit_dyadic, h_limit_dyadic⟩ :=
    CompleteSpace.complete h_cauchy_seq
  have h_limit_tendsto : Tendsto (fun n => I (δ / 2 ^ n)) atTop (𝓝 limit_dyadic) :=
    h_limit_dyadic
  use limit_dyadic
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro η hη_pos
  have h_half_pos : 0 < η / 2 := by linarith
  rw [Metric.tendsto_atTop] at h_limit_tendsto
  obtain ⟨N₁, hN₁⟩ := h_limit_tendsto (η / 2) h_half_pos
  have h_pow_unbounded : ∃ N₂ : ℕ, K * δ / 2 ^ N₂ < η / 4 := by
    have : Tendsto (fun n : ℕ => K * δ / 2 ^ n) atTop (𝓝 0) := by
      have h_tendsto_pow : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
        tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
      have h_tendsto_inv : Tendsto (fun n : ℕ => 1 / (2 : ℝ) ^ n) atTop (𝓝 0) := by
        simp_rw [one_div]; exact tendsto_inv_atTop_zero.comp h_tendsto_pow
      convert Tendsto.const_mul (K * δ) h_tendsto_inv using 1 <;> [ext n; skip] <;> ring
    rw [Metric.tendsto_atTop] at this
    obtain ⟨N₂, hN₂⟩ := this (η / 4) (by linarith)
    refine ⟨N₂, ?_⟩
    specialize hN₂ N₂ le_rfl
    rw [Real.dist_eq, sub_zero,
      abs_of_pos (div_pos (mul_pos hK_pos hδ_pos) (by positivity))] at hN₂
    exact hN₂
  obtain ⟨N₂, hN₂⟩ := h_pow_unbounded
  let N := max N₁ N₂
  use δ / 2 ^ N
  constructor
  · exact div_pos hδ_pos (by positivity)
  · intro ε hε_dist hε_pos
    have hε_pos' : 0 < ε := Set.mem_Ioi.mp hε_dist
    have hε_lt_dyadic : ε < δ / 2 ^ N := by
      rwa [Real.dist_eq, sub_zero, abs_of_pos hε_pos'] at hε_pos
    have h_tri := dist_triangle (I ε) (I (δ / 2 ^ N)) limit_dyadic
    have h_second : dist (I (δ / 2 ^ N)) limit_dyadic < η / 2 := hN₁ N (le_max_left _ _)
    have h_first : dist (I ε) (I (δ / 2 ^ N)) ≤ 2 * K * δ / 2 ^ N := by
      rw [dist_eq_norm]
      have hε_le_δ : ε ≤ δ := le_trans (le_of_lt hε_lt_dyadic)
        (div_le_self hδ_pos.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)))
      obtain ⟨M, hM_lower, hM_upper⟩ := exists_dyadic_bracket hδ_pos hε_pos' hε_le_δ
      have hM_ge_N : M ≥ N := by
        by_contra h_lt
        push Not at h_lt
        have hM1_le_N : M + 1 ≤ N := h_lt
        have h_pow_le : (2 : ℝ) ^ (M + 1) ≤ 2 ^ N :=
          pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hM1_le_N
        have h_div_ge : δ / 2 ^ (M + 1) ≥ δ / 2 ^ N :=
          div_le_div_of_nonneg_left hδ_pos.le (by positivity) h_pow_le
        linarith
      have h_first_piece : ‖I ε - I (δ / 2 ^ M)‖ ≤ K * δ / 2 ^ M := by
        have h_ratio_M : δ / 2 ^ M ≤ 2 * ε := by
          have : δ / 2 ^ M = 2 * (δ / 2 ^ (M + 1)) := by rw [pow_succ]; ring
          linarith
        have h_bound := h_step_uniform (δ / 2 ^ M) ε hε_pos' hM_upper h_ratio_M (h_dyadic_lt M)
        calc ‖I ε - I (δ / 2 ^ M)‖
            ≤ K * (δ / 2 ^ M) := h_bound
          _ = K * δ / 2 ^ M := by ring
      by_cases hMN : M = N
      · subst hMN
        have hKδN_nonneg : 0 ≤ K * δ / 2 ^ N := by positivity
        calc ‖I ε - I (δ / 2 ^ N)‖
            ≤ K * δ / 2 ^ N := h_first_piece
          _ ≤ K * δ / 2 ^ N + K * δ / 2 ^ N := by linarith
          _ = 2 * K * δ / 2 ^ N := by ring
      · have hM_gt_N : M > N := Nat.lt_of_le_of_ne hM_ge_N (Ne.symm hMN)
        have h_tri_inner : ‖I ε - I (δ / 2 ^ N)‖ ≤
            ‖I ε - I (δ / 2 ^ M)‖ + ‖I (δ / 2 ^ M) - I (δ / 2 ^ N)‖ := by
          rw [show I ε - I (δ / 2 ^ N) =
            (I ε - I (δ / 2 ^ M)) + (I (δ / 2 ^ M) - I (δ / 2 ^ N)) from by ring]
          exact norm_add_le _ _
        let J : ℕ → ℂ := fun n => I (δ / 2 ^ n)
        have h_step_J : ∀ n, ‖J (n + 1) - J n‖ ≤ K * δ / 2 ^ n := fun n => by
          simp only [J]; exact h_step n
        have h_sum_bound : ‖I (δ / 2 ^ M) - I (δ / 2 ^ N)‖ ≤
            2 * K * δ / 2 ^ N - 2 * K * δ / 2 ^ M := by
          have h_bound := telescoping_sum_bound hK_pos hδ_pos h_step_J N M hM_gt_N
          simp only [J] at h_bound; exact h_bound
        calc ‖I ε - I (δ / 2 ^ N)‖
            ≤ ‖I ε - I (δ / 2 ^ M)‖ + ‖I (δ / 2 ^ M) - I (δ / 2 ^ N)‖ := h_tri_inner
          _ ≤ K * δ / 2 ^ M + (2 * K * δ / 2 ^ N - 2 * K * δ / 2 ^ M) := by
              linarith [h_first_piece, h_sum_bound]
          _ = 2 * K * δ / 2 ^ N - K * δ / 2 ^ M := by ring
          _ ≤ 2 * K * δ / 2 ^ N := by
              linarith [show (0 : ℝ) ≤ K * δ / 2 ^ M from by positivity]
    have hN_ge_N₂ : N ≥ N₂ := le_max_right _ _
    have h_pow_le : (2 : ℝ) ^ N₂ ≤ 2 ^ N :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hN_ge_N₂
    have h_step_small : K * δ / 2 ^ N ≤ K * δ / 2 ^ N₂ :=
      div_le_div_of_nonneg_left (mul_nonneg hK_pos.le hδ_pos.le) (by positivity) h_pow_le
    have h_Kδ_bound : K * δ / 2 ^ N < η / 4 := lt_of_le_of_lt h_step_small hN₂
    have h_first_small : 2 * K * δ / 2 ^ N < η / 2 := by
      rw [show 2 * K * δ / 2 ^ N = 2 * (K * δ / 2 ^ N) from by ring,
          show (η : ℝ) / 2 = 2 * (η / 4) from by ring]
      exact mul_lt_mul_of_pos_left h_Kδ_bound (by norm_num : (0 : ℝ) < 2)
    calc dist (I ε) limit_dyadic
        ≤ dist (I ε) (I (δ / 2 ^ N)) + dist (I (δ / 2 ^ N)) limit_dyadic := h_tri
      _ ≤ 2 * K * δ / 2 ^ N + dist (I (δ / 2 ^ N)) limit_dyadic := by linarith
      _ < 2 * K * δ / 2 ^ N + η / 2 := by linarith
      _ < η / 2 + η / 2 := by linarith
      _ = η := by ring

lemma measurableSet_norm_gt_of_continuousOn {f : ℝ → ℂ} {s : Set ℝ}
    (ε : ℝ) (hf : ContinuousOn f s) (hs : MeasurableSet s) :
    MeasurableSet ({t | ε < ‖f t‖} ∩ s) := by
  have h_norm_cont : ContinuousOn (fun t => ‖f t‖) s := hf.norm
  have h_open_sub : IsOpen ((s.restrict (fun t => ‖f t‖)) ⁻¹' Ioi ε) :=
    isOpen_Ioi.preimage h_norm_cont.restrict
  rw [isOpen_induced_iff] at h_open_sub
  obtain ⟨U, hU_open, hU_eq⟩ := h_open_sub
  have h_eq : {t | ε < ‖f t‖} ∩ s = U ∩ s := by
    ext x
    constructor
    · intro ⟨hx_far, hx_s⟩
      refine ⟨?_, hx_s⟩
      have h1 : (⟨x, hx_s⟩ : ↑s) ∈ (s.restrict (fun t => ‖f t‖)) ⁻¹' Ioi ε := by
        simp only [mem_preimage, restrict_apply, mem_Ioi]; exact hx_far
      rw [← hU_eq] at h1; exact h1
    · intro ⟨hx_U, hx_s⟩
      refine ⟨?_, hx_s⟩
      have h1 : (⟨x, hx_s⟩ : ↑s) ∈ Subtype.val ⁻¹' U := hx_U
      rw [hU_eq] at h1
      simp only [mem_preimage, restrict_apply, mem_Ioi] at h1; exact h1
  rw [h_eq]; exact hU_open.measurableSet.inter hs

lemma measurableSet_norm_gt_Icc {f : ℝ → ℂ} {a b : ℝ}
    (ε : ℝ) (hf : ContinuousOn f (Icc a b)) :
    MeasurableSet ({t | ε < ‖f t‖} ∩ Icc a b) :=
  measurableSet_norm_gt_of_continuousOn ε hf isClosed_Icc.measurableSet

theorem aEStronglyMeasurable_pv_integrand_piecewiseC1
    {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {ε : ℝ} {P : Finset ℝ}
    (hf : ContinuousOn f (γ '' Icc a b \ Metric.ball z₀ ε))
    (hγ : ContinuousOn γ (Icc a b))
    (hγ'_off_P : ContinuousOn (deriv γ) ((Icc a b) \ P)) :
    AEStronglyMeasurable (fun t => if ε < ‖γ t - z₀‖ then f (γ t) * deriv γ t else 0)
      (volume.restrict (Icc a b)) := by
  let S := {t | ε < ‖γ t - z₀‖}
  have hS_meas : MeasurableSet (S ∩ Icc a b) :=
    measurableSet_norm_gt_Icc ε (hγ.sub continuousOn_const)
  have h_cont : ContinuousOn (fun t => f (γ t) * deriv γ t)
      ((S ∩ Icc a b) \ P) := by
    intro t ⟨⟨ht_S, ht_Icc⟩, ht_nP⟩
    have hγt_not_ball : γ t ∉ Metric.ball z₀ ε := by
      simp only [S, mem_setOf_eq] at ht_S
      simp only [Metric.mem_ball, not_lt, dist_eq_norm]; exact le_of_lt ht_S
    have hγt_in : γ t ∈ γ '' Icc a b \ Metric.ball z₀ ε :=
      ⟨mem_image_of_mem γ ht_Icc, hγt_not_ball⟩
    have h_maps : MapsTo γ ((S ∩ Icc a b) \ P)
        (γ '' Icc a b \ Metric.ball z₀ ε) := by
      intro s ⟨⟨hs_S, hs_Icc⟩, _⟩
      refine ⟨mem_image_of_mem γ hs_Icc, ?_⟩
      simp only [S, mem_setOf_eq] at hs_S
      simp only [Metric.mem_ball, not_lt, dist_eq_norm]; exact le_of_lt hs_S
    exact ((hf (γ t) hγt_in).comp
      ((hγ t ht_Icc).mono (diff_subset.trans inter_subset_right)) h_maps).mul
      ((hγ'_off_P t ⟨ht_Icc, ht_nP⟩).mono
        (by intro x ⟨⟨_, hx_Icc⟩, hx_nP⟩; exact ⟨hx_Icc, hx_nP⟩))
  have h_base_meas : AEStronglyMeasurable (fun t => f (γ t) * deriv γ t)
      (volume.restrict (S ∩ Icc a b)) := by
    have h_diff_meas : MeasurableSet ((S ∩ Icc a b) \ P) :=
      hS_meas.diff P.finite_toSet.measurableSet
    have hP_meas_zero : volume (↑P ∩ (S ∩ Icc a b)) = 0 :=
      (P.finite_toSet.inter_of_left _).measure_zero volume
    have hP_inter_meas : MeasurableSet (↑P ∩ (S ∩ Icc a b)) :=
      P.finite_toSet.measurableSet.inter hS_meas
    have h_disj : Disjoint ((S ∩ Icc a b) \ P) (↑P ∩ (S ∩ Icc a b)) := by
      rw [disjoint_left]; intro x ⟨_, hx_nP⟩ ⟨hx_P, _⟩; exact hx_nP hx_P
    have h_eq : volume.restrict (S ∩ Icc a b) =
        volume.restrict ((S ∩ Icc a b) \ P) +
          volume.restrict (↑P ∩ (S ∩ Icc a b)) := by
      rw [← Measure.restrict_union h_disj hP_inter_meas]
      congr 1; ext x; simp only [mem_union, mem_diff, mem_inter_iff]; tauto
    rw [h_eq]
    apply AEStronglyMeasurable.add_measure (h_cont.aestronglyMeasurable (μ := volume) h_diff_meas)
    simp only [Measure.restrict_eq_zero.mpr hP_meas_zero]
    exact aestronglyMeasurable_zero_measure _
  have h_piecewise : AEStronglyMeasurable
      ((S ∩ Icc a b).piecewise (fun t => f (γ t) * deriv γ t) (fun _ => (0 : ℂ))) volume :=
    AEStronglyMeasurable.piecewise hS_meas h_base_meas aestronglyMeasurable_const
  have h_eq : (fun t => if ε < ‖γ t - z₀‖ then f (γ t) * deriv γ t else 0)
      =ᵐ[volume.restrict (Icc a b)]
      (S ∩ Icc a b).piecewise (fun t => f (γ t) * deriv γ t) (fun _ => 0) := by
    filter_upwards [ae_restrict_mem isClosed_Icc.measurableSet] with t ht
    simp only [piecewise]
    by_cases ht_S : t ∈ S
    · simp only [show t ∈ S ∩ Icc a b from ⟨ht_S, ht⟩, ↓reduceIte,
        show ε < ‖γ t - z₀‖ from ht_S, ↓reduceIte]
    · simp only [show t ∉ S ∩ Icc a b from fun h => ht_S h.1, ↓reduceIte, S,
        mem_setOf_eq, not_lt] at ht_S ⊢
      simp only [not_lt.mpr ht_S, ↓reduceIte]
  exact (h_piecewise.mono_measure Measure.restrict_le_self).congr h_eq.symm


lemma indicator_integrand_deriv_eq (γ : ℝ → ℂ) (c : ℂ) (ε : ℝ) (t : ℝ) :
    (if ‖γ t - c‖ > ε then (γ t - c)⁻¹ * deriv (fun s => γ s - c) t else 0) =
    (if ‖γ t - c‖ > ε then (γ t - c)⁻¹ * deriv γ t else 0) := by
  split_ifs with h
  · congr 1; exact deriv_sub_const c
  · rfl

lemma cpv_exists_from_shifted_tendsto (γ : ℝ → ℂ) (a b : ℝ) (c : ℂ) (L : ℂ)
    (h : Tendsto (fun ε => ∫ t in a..b, if ‖γ t - c‖ > ε
      then (γ t - c)⁻¹ * deriv (fun s => γ s - c) t else 0) (𝓝[>] 0) (𝓝 L)) :
    CauchyPrincipalValueExists' (fun z => (z - c)⁻¹) γ a b c := by
  refine ⟨L, h.congr (fun ε => intervalIntegral.integral_congr (fun t _ => ?_))⟩
  simp only [deriv_sub_const]

lemma arc_angle_injective {t t' : ℝ}
    (ht : t ∈ Set.Ioo (1 : ℝ) 3) (ht' : t' ∈ Set.Ioo (1 : ℝ) 3)
    (h_eq : Complex.exp (↑(Real.pi * (1 + t) / 6) * I) =
            Complex.exp (↑(Real.pi * (1 + t') / 6) * I)) :
    t = t' := by
  rw [Complex.exp_eq_exp_iff_exists_int] at h_eq
  obtain ⟨n, hn⟩ := h_eq
  have h_vals : Real.pi * (1 + t) / 6 - Real.pi * (1 + t') / 6 = 2 * Real.pi * ↑n := by
    have : (↑(Real.pi * (1 + t) / 6) : ℂ) * I - ↑(Real.pi * (1 + t') / 6) * I =
        ↑(2 * Real.pi * ↑n) * I := by
      rw [hn]; push_cast; ring
    have h2 : (↑(Real.pi * (1 + t) / 6 - Real.pi * (1 + t') / 6) : ℂ) * I =
        ↑(2 * Real.pi * ↑n) * I := by
      rw [show (↑(Real.pi * (1 + t) / 6 - Real.pi * (1 + t') / 6) : ℂ) * I =
          ↑(Real.pi * (1 + t) / 6) * I - ↑(Real.pi * (1 + t') / 6) * I from by push_cast; ring]
      exact this
    exact_mod_cast Complex.ofReal_injective (mul_right_cancel₀ I_ne_zero h2)
  have h_diff_small : |Real.pi * (1 + t) / 6 - Real.pi * (1 + t') / 6| < Real.pi := by
    rw [abs_lt]; constructor <;> nlinarith [Real.pi_pos, ht.1, ht.2, ht'.1, ht'.2]
  have hn0 : n = 0 := by
    by_contra h_ne
    have h1 : |(n : ℝ)| ≥ 1 := by exact_mod_cast Int.one_le_abs h_ne
    have h2 : 2 * Real.pi ≤ |2 * Real.pi * (n : ℝ)| := by
      rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      exact le_mul_of_one_le_right (by positivity) h1
    have h3 : |2 * Real.pi * (n : ℝ)| < Real.pi := by rwa [h_vals] at h_diff_small
    linarith [Real.pi_pos]
  rw [hn0] at h_vals; simp only [Int.cast_zero, mul_zero] at h_vals
  nlinarith [Real.pi_ne_zero, Real.pi_pos]

/-- CPV trivially exists when the curve avoids `z₀` on `[a, b]`. -/
lemma cpv_avoidance (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ)
    (h_cont : ContinuousOn γ (Set.Icc a b)) (hab : a ≤ b)
    (h_avoid : ∀ t ∈ Set.Icc a b, γ t ≠ z₀) :
    CauchyPrincipalValueExists' f γ a b z₀ := by
  have h_cont_norm : ContinuousOn (fun t => ‖γ t - z₀‖) (Set.Icc a b) :=
    (h_cont.sub continuousOn_const).norm
  obtain ⟨t₀, ht₀, ht₀_min⟩ := isCompact_Icc.exists_isMinOn
    ⟨a, Set.left_mem_Icc.mpr hab⟩ h_cont_norm
  have hδ : 0 < ‖γ t₀ - z₀‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (h_avoid t₀ ht₀))
  set C := ∫ t in a..b, f (γ t) * deriv γ t
  refine ⟨C, ?_⟩
  apply Tendsto.congr' _ tendsto_const_nhds
  rw [Filter.EventuallyEq, Filter.eventually_iff_exists_mem]
  refine ⟨Set.Ioo 0 ‖γ t₀ - z₀‖, Ioo_mem_nhdsGT hδ, fun ε hε => ?_⟩
  simp only [Set.mem_Ioo] at hε
  exact intervalIntegral.integral_congr (fun t ht => by
    rw [Set.uIcc_of_le hab] at ht
    exact (if_pos (lt_of_lt_of_le hε.2 (ht₀_min ht))).symm)

/-- CPV on adjacent intervals can be concatenated (when `a ≤ b ≤ c`). -/
lemma cpv_concat (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b c : ℝ) (z₀ : ℂ)
    (h_ab : CauchyPrincipalValueExists' f γ a b z₀)
    (h_bc : CauchyPrincipalValueExists' f γ b c z₀)
    (hab : a ≤ b) (hbc : b ≤ c)
    (h_int : ∀ ε > 0, IntervalIntegrable
        (fun t => if ε < ‖γ t - z₀‖ then f (γ t) * deriv γ t else 0) volume a c) :
    CauchyPrincipalValueExists' f γ a c z₀ := by
  obtain ⟨L₁, hL₁⟩ := h_ab
  obtain ⟨L₂, hL₂⟩ := h_bc
  refine ⟨L₁ + L₂, ?_⟩
  apply Tendsto.congr' _ (hL₁.add hL₂)
  rw [Filter.EventuallyEq]
  filter_upwards [self_mem_nhdsWithin] with ε hε
  simp only [Set.mem_Ioi] at hε
  have hII := h_int ε hε
  have hac := hab.trans hbc
  exact intervalIntegral.integral_add_adjacent_intervals
    (hII.mono_set (by
      rw [Set.uIcc_of_le hab, Set.uIcc_of_le hac]; exact Set.Icc_subset_Icc_right hbc))
    (hII.mono_set (by
      rw [Set.uIcc_of_le hbc, Set.uIcc_of_le hac]; exact Set.Icc_subset_Icc_left hab))

end
