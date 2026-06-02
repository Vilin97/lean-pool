/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.GeneralizedResidueTheory.Residue.FlatnessTransfer.PerTermVanishing
import LeanPool.LeanModularForms.GeneralizedResidueTheory.Residue.FlatnessTransfer.PerTermVanishing.CPVHelpers
import LeanPool.LeanModularForms.GeneralizedResidueTheory.Residue.MeromorphicPrincipalPart

/-!
# Higher-Order Cancellation Assembly

Assembles the per-term vanishing results into the full higher-order cancellation
proof. The abstract theorem `higherOrderCancel_assembly_abstract` takes two
callback hypotheses (holomorphic vanishing and finset vanishing) that are
instantiated differently for convex vs null-homologous domains.

## Main results

* `higherOrderCancel_assembly_abstract`: abstract assembly with callback hypotheses

The convex-domain specializations (`higherOrderCancel_assembly`,
`conditionsAB_imply_higherOrderCancel`) are in `FlatnessTransfer.lean`.
-/

open Complex MeasureTheory Set Filter Topology Finset Real
open scoped Interval

noncomputable section

namespace GeneralizedResidueTheory

private theorem differentiableOn_ppMinusRes (f : ℂ → ℂ) (s : ℂ)
    (hMero_s : MeromorphicAt f s) :
    DifferentiableOn ℂ (fun z => meromorphicPrincipalPart f s z - residueAt f s / (z - s))
      ({s}ᶜ : Set ℂ) :=
  DifferentiableOn.sub
    (meromorphicPrincipalPart_differentiableOn f s hMero_s)
    (DifferentiableOn.div (differentiableOn_const _)
      (differentiableOn_id.sub (differentiableOn_const _))
      (fun _ hz => sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hz)))

private theorem residueAt_eq_zero_of_analyticExpansion (f : ℂ → ℂ) (s : ℂ)
    (g_loc : ℂ → ℂ) (hg_loc_an : AnalyticAt ℂ g_loc s)
    (hf_eq_loc : ∀ᶠ (z : ℂ) in 𝓝[≠] s, f z = g_loc z) :
    residueAt f s = 0 := by
  unfold residueAt
  apply Filter.Tendsto.limUnder_eq
  obtain ⟨rg, hrg_pos, hg_ball⟩ := hg_loc_an.exists_ball_analyticOnNhd
  rw [Filter.Eventually, Metric.mem_nhdsWithin_iff] at hf_eq_loc
  obtain ⟨rf, hrf_pos, hrf_eq⟩ := hf_eq_loc
  have hr₀_pos : 0 < min rg rf := lt_min hrg_pos hrf_pos
  apply tendsto_nhds_of_eventually_eq
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Iio_mem_nhds hr₀_pos] with r hr_lt hr_pos
  simp only [Set.mem_Ioi] at hr_pos; simp only [Set.mem_Iio] at hr_lt
  have hr_lt_rg : r < rg := lt_of_lt_of_le hr_lt (min_le_left _ _)
  have hr_lt_rf : r < rf := lt_of_lt_of_le hr_lt (min_le_right _ _)
  have h_eq_on : ∀ z ∈ Metric.sphere s r, f z = g_loc z := by
    intro z hz
    have hne : z ≠ s := by
      intro h; rw [h, Metric.mem_sphere, dist_self] at hz; linarith
    have h_in : z ∈ Metric.ball s rf ∩ {s}ᶜ :=
      ⟨Metric.mem_ball.mpr (by rw [Metric.mem_sphere.mp hz]; exact hr_lt_rf),
       Set.mem_compl_singleton_iff.mpr hne⟩
    exact hrf_eq h_in
  have hg_cont : ContinuousOn g_loc (Metric.closedBall s r) :=
    hg_ball.continuousOn.mono (Metric.closedBall_subset_ball hr_lt_rg)
  have hg_diff : DifferentiableOn ℂ g_loc (Metric.ball s r) := by
    intro z hz; exact (hg_ball z (Metric.ball_subset_ball hr_lt_rg.le hz)
      ).differentiableAt.differentiableWithinAt
  have hg_ci_zero : (∮ z in C(s, r), g_loc z) = 0 :=
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
      hr_pos.le Set.countable_empty hg_cont
      (fun z ⟨hz, _⟩ => hg_diff.differentiableAt
        (Metric.isOpen_ball.mem_nhds hz))
  have hf_ci : (∮ z in C(s, r), f z) =
      (∮ z in C(s, r), g_loc z) :=
    circleIntegral.integral_congr hr_pos.le h_eq_on
  simp [hf_ci, hg_ci_zero]

private theorem meromorphicAt_ppMinusRes (f : ℂ → ℂ) (s : ℂ) (hMero_s : MeromorphicAt f s) :
    MeromorphicAt (fun z => meromorphicPrincipalPart f s z - residueAt f s / (z - s)) s := by
  obtain ⟨g_rp, hg_rp_an, hg_rp_eq⟩ :=
    meromorphicAt_sub_principalPart_eventually f s hMero_s
  have h_pp_eq : (fun z => f z - g_rp z) =ᶠ[𝓝[≠] s]
      meromorphicPrincipalPart f s := by
    filter_upwards [hg_rp_eq] with z hz
    linear_combination hz
  have h_pp_mero : MeromorphicAt (meromorphicPrincipalPart f s) s :=
    (hMero_s.fun_sub hg_rp_an.meromorphicAt).congr h_pp_eq
  exact h_pp_mero.fun_sub
    ((MeromorphicAt.const (residueAt f s) s).fun_div
      ((MeromorphicAt.id s).fun_sub (MeromorphicAt.const s s)))

private theorem laurent_coeff_le_poleOrder (f : ℂ → ℂ) (s : ℂ)
    (hMero_s : MeromorphicAt f s) {N_s : ℕ} (a_s : Fin N_s → ℂ)
    (g_loc : ℂ → ℂ) (hg_loc_an : AnalyticAt ℂ g_loc s)
    (hf_eq_loc : ∀ᶠ (z : ℂ) in 𝓝[≠] s,
      f z = g_loc z + ∑ k : Fin N_s, a_s k / (z - s) ^ (k.val + 1))
    {kv : ℕ} {hkv : kv < N_s} (ha_zero : a_s ⟨kv, hkv⟩ ≠ 0) :
    kv + 1 ≤ poleOrderAt f s := by
  unfold poleOrderAt
  let nonzero_idx := (Finset.univ : Finset (Fin N_s)).filter
    (fun k => a_s k ≠ 0)
  have h_ne : nonzero_idx.Nonempty :=
    ⟨⟨kv, hkv⟩, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ha_zero⟩⟩
  set m_idx := (nonzero_idx.max' h_ne) with hm_def
  have hm_ne : a_s m_idx ≠ 0 :=
    (Finset.mem_filter.mp (nonzero_idx.max'_mem h_ne)).2
  have hkv_le_m : kv ≤ m_idx.val :=
    Finset.le_max' nonzero_idx ⟨kv, hkv⟩
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha_zero⟩)
  have hm_max : ∀ k : Fin N_s, a_s k ≠ 0 → k ≤ m_idx :=
    fun k hk => Finset.le_max' nonzero_idx k
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩)
  suffices h_ord : meromorphicOrderAt f s =
      ↑(-(↑(m_idx.val + 1) : ℤ)) by
    rw [h_ord]; simp only [WithTop.untop₀_coe, neg_neg, Int.toNat_natCast]
    omega
  rw [meromorphicOrderAt_eq_int_iff hMero_s]
  refine ⟨fun z => (z - s) ^ (m_idx.val + 1) * g_loc z +
    ∑ k : Fin N_s, a_s k * (z - s) ^ (m_idx.val - k.val), ?_, ?_, ?_⟩
  · exact ((analyticAt_id.sub analyticAt_const).pow _).mul hg_loc_an |>.add
      (Finset.analyticAt_fun_sum Finset.univ
        (fun k _ => analyticAt_const.mul
          ((analyticAt_id.sub analyticAt_const).pow _)))
  · simp only [sub_self, zero_pow (Nat.succ_ne_zero _), zero_mul, zero_add]
    have : ∑ k : Fin N_s, a_s k * (0 : ℂ) ^ (m_idx.val - k.val) =
        a_s m_idx := by
      rw [Finset.sum_eq_single m_idx]
      · simp only [Nat.sub_self, pow_zero, mul_one]
      · intro k _ hk
        by_cases hkm : k.val < m_idx.val
        · simp [zero_pow (by omega : m_idx.val - k.val ≠ 0)]
        · push Not at hkm
          have hk_gt : m_idx < k :=
            lt_of_le_of_ne (Fin.mk_le_mk.mpr hkm) (Ne.symm hk)
          have := hm_max k
          have hk_eq : a_s k = 0 := by
            by_contra ha; exact absurd (this ha) (not_le.mpr hk_gt)
          simp only [hk_eq, zero_mul]
      · intro h; exact absurd (Finset.mem_univ m_idx) h
    rw [this]; exact hm_ne
  · filter_upwards [hf_eq_loc, self_mem_nhdsWithin] with z hfz hz
    rw [smul_eq_mul, hfz]
    have hzs_ne : z - s ≠ 0 := sub_ne_zero.mpr hz
    rw [mul_add, ← mul_assoc,
      zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hzs_ne),
      one_mul]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk_le : k.val ≤ m_idx.val
    · have hpow_k : (z - s) ^ (k.val + 1) ≠ 0 := pow_ne_zero _ hzs_ne
      have hpow_m : (z - s) ^ (m_idx.val + 1) ≠ 0 := pow_ne_zero _ hzs_ne
      field_simp
      rw [mul_assoc (a_s k), ← pow_add,
        show k.val + 1 + (m_idx.val - k.val) = m_idx.val + 1 from by omega]
    · push Not at hk_le
      by_cases ha_k : a_s k = 0
      · simp [ha_k]
      · exact absurd (hm_max k ha_k) (not_le.mpr hk_le)

private theorem residueAt_ppMinusRes_eq_zero (f : ℂ → ℂ) (s : ℂ)
    (hMero_s : MeromorphicAt f s) :
    residueAt (fun z => meromorphicPrincipalPart f s z - residueAt f s / (z - s)) s = 0 := by
  have h_single := residueAt_sub_residueSum_eq_zero {s} f s
    (Finset.mem_singleton.mpr rfl) hMero_s
  simp only [Finset.sum_singleton] at h_single
  obtain ⟨g_rp, hg_rp_an, hg_rp_eq⟩ :=
    meromorphicAt_sub_principalPart_eventually f s hMero_s
  obtain ⟨rg, hrg_pos, hg_ball⟩ := hg_rp_an.exists_ball_analyticOnNhd
  have h_ev_mem : {z | f z - meromorphicPrincipalPart f s z = g_rp z} ∈ 𝓝[≠] s :=
    hg_rp_eq
  rw [Metric.mem_nhdsWithin_iff] at h_ev_mem
  obtain ⟨rp, hrp_pos, hrp_eq⟩ := h_ev_mem
  set ρ' := min rg rp with hρ'_def
  have hρ'_pos : 0 < ρ' := lt_min hrg_pos hrp_pos
  have h_ci_agree : ∀ r, 0 < r → r < ρ' →
      (∮ z in C(s, r), (fun z => meromorphicPrincipalPart f s z - residueAt f s / (z - s)) z) =
      (∮ z in C(s, r), (fun z => f z - residueAt f s / (z - s)) z) := by
    intro r hr_pos hr_lt
    have hr_lt_rg : r < rg := lt_of_lt_of_le hr_lt (min_le_left _ _)
    have hr_lt_rp : r < rp := lt_of_lt_of_le hr_lt (min_le_right _ _)
    have h_eq_on : ∀ z ∈ Metric.sphere s r,
        (fun z => meromorphicPrincipalPart f s z - residueAt f s / (z - s)) z =
        (fun z => f z - residueAt f s / (z - s)) z - g_rp z := by
      intro z hz
      have hne : z ≠ s := by
        intro heq; rw [heq, Metric.mem_sphere, dist_self] at hz; linarith
      have h_in : z ∈ Metric.ball s rp ∩ {s}ᶜ :=
        ⟨Metric.mem_ball.mpr (by rw [Metric.mem_sphere.mp hz]; exact hr_lt_rp),
         Set.mem_compl_singleton_iff.mpr hne⟩
      have hfpp := hrp_eq h_in
      simp only [Set.mem_setOf_eq] at hfpp
      simp only
      change meromorphicPrincipalPart f s z - residueAt f s / (z - s) =
        f z - residueAt f s / (z - s) - g_rp z
      linear_combination -hfpp
    have hg_cont : ContinuousOn g_rp (Metric.closedBall s r) :=
      hg_ball.continuousOn.mono (Metric.closedBall_subset_ball hr_lt_rg)
    have hg_diff : DifferentiableOn ℂ g_rp (Metric.ball s r) := by
      intro z hz
      have := hg_ball z
        (Metric.ball_subset_ball hr_lt_rg.le hz)
      exact this.differentiableAt.differentiableWithinAt
    have hg_ci_zero : (∮ z in C(s, r), g_rp z) = 0 :=
      Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
        hr_pos.le Set.countable_empty hg_cont
        (fun z ⟨hz, _⟩ => hg_diff.differentiableAt
          (Metric.isOpen_ball.mem_nhds hz))
    have hg_ci : CircleIntegrable g_rp s r :=
      hg_cont.mono Metric.sphere_subset_closedBall |>.circleIntegrable hr_pos.le
    have h_sphere_sub : Metric.sphere s r ⊆ ({s}ᶜ : Set ℂ) := by
      intro z hz heq; rw [heq, Metric.mem_sphere, dist_self] at hz; linarith
    have h_term_diff_compl : DifferentiableOn ℂ
        (fun z => meromorphicPrincipalPart f s z - residueAt f s / (z - s)) ({s}ᶜ : Set ℂ) :=
      differentiableOn_ppMinusRes f s hMero_s
    have h_term_ci : CircleIntegrable
        (fun z => meromorphicPrincipalPart f s z - residueAt f s / (z - s)) s r :=
      (h_term_diff_compl.continuousOn.mono h_sphere_sub).circleIntegrable hr_pos.le
    have h_add_ci : CircleIntegrable
        (fun z => (meromorphicPrincipalPart f s z - residueAt f s / (z - s)) + g_rp z) s r :=
      h_term_ci.add hg_ci
    have h_split : (∮ z in C(s, r),
        (fun z => (meromorphicPrincipalPart f s z - residueAt f s / (z - s)) + g_rp z) z) =
      (∮ z in C(s, r), (fun z => meromorphicPrincipalPart f s z - residueAt f s / (z - s)) z) +
        (∮ z in C(s, r), g_rp z) :=
      circleIntegral.integral_add h_term_ci hg_ci
    have h_sum_eq : ∀ z ∈ Metric.sphere s r,
        (fun z => (meromorphicPrincipalPart f s z - residueAt f s / (z - s)) + g_rp z) z =
        (fun z => f z - residueAt f s / (z - s)) z := by
      intro z hz
      have := h_eq_on z hz
      simp only
      linear_combination this
    have h_int_eq : (∮ z in C(s, r),
        (fun z => (meromorphicPrincipalPart f s z - residueAt f s / (z - s)) + g_rp z) z) =
      (∮ z in C(s, r), (fun z => f z - residueAt f s / (z - s)) z) :=
      circleIntegral.integral_congr hr_pos.le h_sum_eq
    calc (∮ z in C(s, r), (fun z =>
            meromorphicPrincipalPart f s z - residueAt f s / (z - s)) z)
        = (∮ z in C(s, r), (fun z =>
            meromorphicPrincipalPart f s z -
              residueAt f s / (z - s)) z) + 0 := (add_zero _).symm
      _ = (∮ z in C(s, r), (fun z =>
            meromorphicPrincipalPart f s z -
              residueAt f s / (z - s)) z) +
          (∮ z in C(s, r), g_rp z) := by rw [hg_ci_zero]
      _ = (∮ z in C(s, r), (fun z =>
            (meromorphicPrincipalPart f s z -
              residueAt f s / (z - s)) + g_rp z) z) :=
          h_split.symm
      _ = (∮ z in C(s, r), (fun z => f z - residueAt f s / (z - s)) z) := h_int_eq
  rw [show residueAt (fun z => meromorphicPrincipalPart f s z - residueAt f s / (z - s)) s =
    residueAt (fun z => f z - residueAt f s / (z - s)) s from by
    simp only [residueAt]
    exact limUnder_eventually_eq (by
      filter_upwards [Ioo_mem_nhdsGT hρ'_pos] with r ⟨hr_pos, hr_lt⟩
      congr 1
      exact h_ci_agree r hr_pos hr_lt)]
  exact h_single

/-- Sum of all meromorphic principal parts over `S0`. -/
private noncomputable def assembly_totalPP (S0 : Finset ℂ) (f : ℂ → ℂ) : ℂ → ℂ :=
  fun z => ∑ s ∈ S0, meromorphicPrincipalPart f s z

/-- The regular part: `f` minus the sum of all principal parts. -/
private noncomputable def assembly_reg (S0 : Finset ℂ) (f : ℂ → ℂ) : ℂ → ℂ :=
  fun z => f z - assembly_totalPP S0 f z

/-- The polar correction: sum of `(pp_s - res_s/(z-s))` over all `s ∈ S0`. -/
private noncomputable def assembly_pol (S0 : Finset ℂ) (f : ℂ → ℂ) : ℂ → ℂ :=
  fun z => ∑ s ∈ S0, (meromorphicPrincipalPart f s z - residueAt f s / (z - s))

/-- The normalized regular part: at poles `s ∈ S0`, uses the correction function
`g_corr` minus other principal parts; away from `S0`, equals `assembly_reg`. -/
private noncomputable def assembly_regNF
    (S0 : Finset ℂ) (f : ℂ → ℂ) (g_corr : ∀ s ∈ S0, ℂ → ℂ) : ℂ → ℂ :=
  fun z => if hz : z ∈ S0 then
    g_corr z hz z - ∑ s' ∈ S0.erase z, meromorphicPrincipalPart f s' z
  else assembly_reg S0 f z

/-- At a pole `z ∈ S0`, `assembly_regNF` is differentiable within `U` because
it agrees in a neighbourhood with the analytic correction minus other principal parts. -/
private theorem assembly_regNF_differentiableWithinAt_pole
    (S0 : Finset ℂ) (f : ℂ → ℂ) (hMero : ∀ s ∈ S0, MeromorphicAt f s)
    (g_corr : ∀ s ∈ S0, ℂ → ℂ)
    (hg_corr_an : ∀ (s : ℂ) (hs : s ∈ S0), AnalyticAt ℂ (g_corr s hs) s)
    (hg_corr_eq : ∀ (s : ℂ) (hs : s ∈ S0),
      ∀ᶠ z in 𝓝[≠] s, f z - meromorphicPrincipalPart f s z = g_corr s hs z)
    (U : Set ℂ) (z : ℂ) (_hz : z ∈ U) (hz_S : z ∈ S0) :
    DifferentiableWithinAt ℂ (assembly_regNF S0 f g_corr) U z := by
  have h_other_pp_diff : DifferentiableAt ℂ
      (fun w => ∑ s' ∈ S0.erase z, meromorphicPrincipalPart f s' w) z := by
    have h_each : ∀ s' ∈ S0.erase z,
        DifferentiableAt ℂ (meromorphicPrincipalPart f s') z := by
      intro s' hs'
      have hne : z ≠ s' := (Finset.ne_of_mem_erase hs').symm
      exact (meromorphicPrincipalPart_differentiableOn f s'
        (hMero s' (Finset.mem_of_mem_erase hs')) z
        (Set.mem_compl_singleton_iff.mpr hne)).differentiableAt
        (isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr hne))
    have h_sum := DifferentiableAt.sum h_each
    rwa [show (fun w => ∑ s' ∈ S0.erase z, meromorphicPrincipalPart f s' w) =
        (∑ s' ∈ S0.erase z, meromorphicPrincipalPart f s') from
      funext (fun w => (Finset.sum_apply w _ _).symm)]
  have h_corr_diff : DifferentiableAt ℂ
      (fun w => g_corr z hz_S w -
        ∑ s' ∈ S0.erase z, meromorphicPrincipalPart f s' w) z :=
    (hg_corr_an z hz_S).differentiableAt.sub h_other_pp_diff
  have h_S_minus_z_closed : IsClosed ((↑(S0.erase z) : Set ℂ)) :=
    (S0.erase z).finite_toSet.isClosed
  have hz_not_erase : z ∉ (↑(S0.erase z) : Set ℂ) :=
    fun hh => (Finset.notMem_erase z S0) (Finset.mem_coe.mp hh)
  have h_compl_open : IsOpen (↑(S0.erase z) : Set ℂ)ᶜ :=
    h_S_minus_z_closed.isOpen_compl
  have hz_in_compl : z ∈ (↑(S0.erase z) : Set ℂ)ᶜ :=
    Set.mem_compl hz_not_erase
  have h_ev : (fun w => g_corr z hz_S w -
      ∑ s' ∈ S0.erase z, meromorphicPrincipalPart f s' w) =ᶠ[𝓝 z]
      assembly_regNF S0 f g_corr := by
    have hg_corr_eq_z := hg_corr_eq z hz_S
    rw [Filter.Eventually, mem_nhdsWithin] at hg_corr_eq_z
    obtain ⟨V, hV_open, hz_V, hV_eq⟩ := hg_corr_eq_z
    apply Filter.Eventually.mono
      ((hV_open.inter h_compl_open).mem_nhds ⟨hz_V, hz_in_compl⟩)
    intro w ⟨hw_V, hw_compl⟩
    change (fun w => g_corr z hz_S w -
      ∑ s' ∈ S0.erase z, meromorphicPrincipalPart f s' w) w =
      assembly_regNF S0 f g_corr w
    simp only [assembly_regNF]
    by_cases hw_S : w ∈ S0
    · have hw_eq : w = z := by
        by_contra hne
        exact hw_compl (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hne, hw_S⟩))
      rw [hw_eq]; simp [hz_S]
    · have hw_ne_z : w ≠ z := fun heq => hw_S (heq ▸ hz_S)
      have h_fw : f w - meromorphicPrincipalPart f z w = g_corr z hz_S w :=
        hV_eq ⟨hw_V, hw_ne_z⟩
      simp only [dif_neg hw_S, assembly_reg, assembly_totalPP]
      rw [show (∑ s ∈ S0, meromorphicPrincipalPart f s w) =
          meromorphicPrincipalPart f z w +
          ∑ s' ∈ S0.erase z, meromorphicPrincipalPart f s' w from
        (Finset.add_sum_erase S0 _ hz_S).symm,
        ← h_fw]
      ring
  exact (h_ev.differentiableAt_iff.mp h_corr_diff).differentiableWithinAt

/-- Away from `S0`, `assembly_regNF` equals `assembly_reg`, so it is differentiable
because `f` and the principal parts are. -/
private theorem assembly_regNF_differentiableWithinAt_regular
    (S0 : Finset ℂ) (f : ℂ → ℂ) (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f (U \ S0)) (hMero : ∀ s ∈ S0, MeromorphicAt f s)
    (g_corr : ∀ s ∈ S0, ℂ → ℂ) (z : ℂ) (hz : z ∈ U) (hz_S : z ∉ S0) :
    DifferentiableWithinAt ℂ (assembly_regNF S0 f g_corr) U z := by
  have hz_punct : z ∈ U \ ↑S0 := ⟨hz, fun hh => hz_S (Finset.mem_coe.mp hh)⟩
  have hU_S_open : IsOpen (U \ ↑S0) := hU.sdiff (S0.finite_toSet.isClosed)
  have hf_da : DifferentiableAt ℂ f z :=
    (hf z hz_punct).differentiableAt (hU_S_open.mem_nhds hz_punct)
  have htp_da : DifferentiableAt ℂ (assembly_totalPP S0 f) z := by
    have h_each : ∀ s ∈ S0,
        DifferentiableAt ℂ (meromorphicPrincipalPart f s) z := by
      intro s hs
      have hne : z ≠ s := fun heq => hz_S (heq ▸ hs)
      exact (meromorphicPrincipalPart_differentiableOn f s (hMero s hs) z
        (Set.mem_compl_singleton_iff.mpr hne)).differentiableAt
        (isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr hne))
    have h_sum := DifferentiableAt.sum h_each
    rwa [show assembly_totalPP S0 f = (∑ s ∈ S0, meromorphicPrincipalPart f s) from
      funext (fun z => (Finset.sum_apply z _ _).symm)]
  have h_reg_diff : DifferentiableAt ℂ (assembly_reg S0 f) z := hf_da.sub htp_da
  have h_ev : assembly_reg S0 f =ᶠ[𝓝 z] assembly_regNF S0 f g_corr := by
    apply Filter.Eventually.mono (hU_S_open.mem_nhds hz_punct)
    intro w ⟨_, hw_not_S⟩
    have hw_not_S' : w ∉ S0 := fun hh => hw_not_S (Finset.mem_coe.mpr hh)
    simp only [assembly_regNF, hw_not_S', dite_false]
  exact (h_ev.differentiableAt_iff.mp h_reg_diff).differentiableWithinAt

/-- The normalized regular part `assembly_regNF` is differentiable on all of `U`. -/
private theorem assembly_regNF_differentiableOn (S0 : Finset ℂ) (f : ℂ → ℂ)
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f (U \ S0))
    (hMero : ∀ s ∈ S0, MeromorphicAt f s) (g_corr : ∀ s ∈ S0, ℂ → ℂ)
    (hg_corr_an : ∀ (s : ℂ) (hs : s ∈ S0), AnalyticAt ℂ (g_corr s hs) s)
    (hg_corr_eq : ∀ (s : ℂ) (hs : s ∈ S0),
      ∀ᶠ z in 𝓝[≠] s, f z - meromorphicPrincipalPart f s z = g_corr s hs z) :
    DifferentiableOn ℂ (assembly_regNF S0 f g_corr) U :=
  fun z hz => by
    by_cases hz_S : z ∈ S0
    · exact assembly_regNF_differentiableWithinAt_pole S0 f hMero g_corr
        hg_corr_an hg_corr_eq U z hz hz_S
    · exact assembly_regNF_differentiableWithinAt_regular S0 f hU hf hMero
        g_corr z hz hz_S

/-- Variant of `cpv_tendsto_zero_of_add_split` where the function agrees with `g₁ + g₂`
off the entire set `S0`, rather than off a single point. -/
private theorem cpv_tendsto_zero_of_add_split_set
    (U : Set ℂ) (S0 : Finset ℂ) (γ : PiecewiseC1Immersion)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U) (g g₁ g₂ : ℂ → ℂ)
    (h_off_S0 : ∀ z, z ∉ (↑S0 : Set ℂ) → g z = g₁ z + g₂ z)
    (h_g₁_cont : ContinuousOn g₁ (U \ ↑S0))
    (h_g₂_cont : ContinuousOn g₂ (U \ ↑S0))
    (h_g₁_cpv : Tendsto (fun ε => ∫ t in γ.a..γ.b,
      cauchyPrincipalValueIntegrandOn S0 g₁ γ.toFun ε t) (𝓝[>] 0) (𝓝 0))
    (h_g₂_cpv : Tendsto (fun ε => ∫ t in γ.a..γ.b,
      cauchyPrincipalValueIntegrandOn S0 g₂ γ.toFun ε t) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε => ∫ t in γ.a..γ.b,
      cauchyPrincipalValueIntegrandOn S0 g γ.toFun ε t) (𝓝[>] 0) (𝓝 0) := by
  rw [show (0 : ℂ) = 0 + 0 from (add_zero 0).symm]
  apply Filter.Tendsto.congr' _ (h_g₁_cpv.add h_g₂_cpv)
  filter_upwards [self_mem_nhdsWithin] with ε (hε : (0 : ℝ) < ε)
  have h_pw_eq : ∀ t, cauchyPrincipalValueIntegrandOn S0 g γ.toFun ε t =
      cauchyPrincipalValueIntegrandOn S0 (fun z => g₁ z + g₂ z) γ.toFun ε t := by
    intro t; simp only [cauchyPrincipalValueIntegrandOn]
    split_ifs with h_near
    · rfl
    · push Not at h_near
      have hγt_not_S0 : (γ.toFun t) ∉ (↑S0 : Set ℂ) := by
        intro hmem
        have hmem' := Finset.mem_coe.mp hmem
        have := h_near (γ.toFun t) hmem'
        rw [sub_self, norm_zero] at this; linarith
      congr 1; exact h_off_S0 (γ.toFun t) hγt_not_S0
  rw [show (fun t => cauchyPrincipalValueIntegrandOn S0 g γ.toFun ε t) =
      fun t => cauchyPrincipalValueIntegrandOn S0
        (fun z => g₁ z + g₂ z) γ.toFun ε t from funext h_pw_eq]
  rw [show (fun t => cauchyPrincipalValueIntegrandOn S0
        (fun z => g₁ z + g₂ z) γ.toFun ε t) =
      fun t => cauchyPrincipalValueIntegrandOn S0 g₁ γ.toFun ε t +
        cauchyPrincipalValueIntegrandOn S0 g₂ γ.toFun ε t from
    funext (fun t => cpvIntegrandOn_add S0 g₁ g₂ γ.toFun ε t)]
  exact (intervalIntegral.integral_add
    (intervalIntegrable_cpvIntegrandOn_of_continuousOn_diff U S0 g₁
      h_g₁_cont γ hγ_in_U ε hε)
    (intervalIntegrable_cpvIntegrandOn_of_continuousOn_diff U S0 g₂
      h_g₂_cont γ hγ_in_U ε hε)).symm

/-- If CPV of each per-pole `g s` tends to 0, then CPV of `∑ s ∈ S0, g s`
also tends to 0. Variant for `Finset` sums (vs. `Fin N` sums). -/
private theorem cpv_tendsto_zero_of_finset_sum (S0 : Finset ℂ)
    (γ : PiecewiseC1Immersion) (U : Set ℂ)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U) (g : ℂ → ℂ → ℂ)
    (h_cont : ∀ s ∈ S0, ContinuousOn (g s) (U \ ↑S0))
    (h_tendsto : ∀ s ∈ S0, Tendsto (fun ε => ∫ t in γ.a..γ.b,
      cauchyPrincipalValueIntegrandOn S0 (g s) γ.toFun ε t) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε => ∫ t in γ.a..γ.b,
      cauchyPrincipalValueIntegrandOn S0
        (fun z => ∑ s ∈ S0, g s z) γ.toFun ε t) (𝓝[>] 0) (𝓝 0) := by
  have h_cpv_sum : ∀ ε t,
      cauchyPrincipalValueIntegrandOn S0 (fun z => ∑ s ∈ S0, g s z) γ.toFun ε t =
      ∑ s ∈ S0, cauchyPrincipalValueIntegrandOn S0 (g s) γ.toFun ε t :=
    fun ε t => cpvIntegrandOn_finset_sum S0 S0 (fun s z => g s z) γ.toFun ε t
  have h_per_s_int : ∀ s ∈ S0, ∀ ε > 0,
      IntervalIntegrable (cauchyPrincipalValueIntegrandOn S0 (g s) γ.toFun ε)
        volume γ.a γ.b :=
    fun s hs ε hε => intervalIntegrable_cpvIntegrandOn_of_continuousOn_diff U S0
      (g s) (h_cont s hs) γ hγ_in_U ε hε
  have h_int_sum : ∀ ε > 0,
      ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0 (fun z => ∑ s ∈ S0, g s z) γ.toFun ε t =
      ∑ s ∈ S0, ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0 (g s) γ.toFun ε t := by
    intro ε hε
    rw [show (fun t => cauchyPrincipalValueIntegrandOn S0
        (fun z => ∑ s ∈ S0, g s z) γ.toFun ε t) = fun t => ∑ s ∈ S0,
        cauchyPrincipalValueIntegrandOn S0 (g s) γ.toFun ε t from
      funext (h_cpv_sum ε)]
    exact intervalIntegral.integral_finsetSum (fun s hs => h_per_s_int s hs ε hε)
  rw [show (0 : ℂ) = ∑ _s ∈ S0, (0 : ℂ) from (Finset.sum_const_zero).symm]
  apply Filter.Tendsto.congr'
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact (h_int_sum ε hε).symm
  · exact tendsto_finsetSum S0 (fun s hs => h_tendsto s hs)

/-- If CPV of each `gₖ` tends to 0, and `gₖ` is CPV-integrable, then CPV of `∑ k, gₖ`
also tends to 0 (for a `Finset.univ` sum over `Fin N`). -/
private theorem cpv_tendsto_zero_of_fin_sum {N : ℕ} (S0 : Finset ℂ)
    (γ : PiecewiseC1Immersion) (U : Set ℂ)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U) (g : Fin N → ℂ → ℂ)
    (h_cont : ∀ k : Fin N, ContinuousOn (g k) (U \ ↑S0))
    (h_tendsto : ∀ k : Fin N, Tendsto (fun ε => ∫ t in γ.a..γ.b,
      cauchyPrincipalValueIntegrandOn S0 (g k) γ.toFun ε t) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε => ∫ t in γ.a..γ.b,
      cauchyPrincipalValueIntegrandOn S0
        (fun z => ∑ k : Fin N, g k z) γ.toFun ε t) (𝓝[>] 0) (𝓝 0) := by
  have h_cpv_decomp : ∀ ε t,
      cauchyPrincipalValueIntegrandOn S0 (fun z => ∑ k : Fin N, g k z) γ.toFun ε t =
      ∑ k : Fin N, cauchyPrincipalValueIntegrandOn S0 (g k) γ.toFun ε t :=
    fun ε t => cpvIntegrandOn_finset_sum S0 Finset.univ (fun k z => g k z) γ.toFun ε t
  have h_per_k_int : ∀ (k : Fin N), ∀ ε > 0,
      IntervalIntegrable (cauchyPrincipalValueIntegrandOn S0 (g k) γ.toFun ε)
        volume γ.a γ.b :=
    fun k ε hε => intervalIntegrable_cpvIntegrandOn_of_continuousOn_diff U S0
      (g k) (h_cont k) γ hγ_in_U ε hε
  have h_int_eq : ∀ ε > 0,
      ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0 (fun z => ∑ k : Fin N, g k z) γ.toFun ε t =
      ∑ k : Fin N, ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0 (g k) γ.toFun ε t := by
    intro ε hε
    rw [show (fun t => cauchyPrincipalValueIntegrandOn S0
        (fun z => ∑ k : Fin N, g k z) γ.toFun ε t) = fun t => ∑ k : Fin N,
        cauchyPrincipalValueIntegrandOn S0 (g k) γ.toFun ε t from
      funext (h_cpv_decomp ε)]
    exact intervalIntegral.integral_finsetSum (fun k _ => h_per_k_int k ε hε)
  have h_sum_tendsto : Tendsto (fun ε => ∑ k : Fin N,
      ∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0 (g k) γ.toFun ε t)
      (𝓝[>] 0) (𝓝 0) := by
    have h0 : (0 : ℂ) = ∑ _k : Fin N, (0 : ℂ) := Finset.sum_const_zero.symm
    conv_rhs => rw [h0]
    exact tendsto_finsetSum Finset.univ (fun k _ => h_tendsto k)
  apply h_sum_tendsto.congr'
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  exact (h_int_eq ε hε).symm

/-- Given two functions whose CPV integrals each tend to 0, and a third function
that agrees with their sum off `S0`, the CPV integral of the third also tends to 0.
Used to combine the error and polar-higher parts. -/
private theorem cpv_tendsto_zero_of_add_split
    (U : Set ℂ) (S0 : Finset ℂ) (γ : PiecewiseC1Immersion)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (g g₁ g₂ : ℂ → ℂ) (s : ℂ) (hs : s ∈ S0)
    (h_off_s : ∀ z, z ≠ s → g z = g₁ z + g₂ z)
    (h_g₁_cont : ContinuousOn g₁ (U \ ↑S0))
    (h_g₂_cont : ContinuousOn g₂ (U \ ↑S0))
    (h_g₁_cpv : Tendsto (fun ε => ∫ t in γ.a..γ.b,
      cauchyPrincipalValueIntegrandOn S0 g₁ γ.toFun ε t) (𝓝[>] 0) (𝓝 0))
    (h_g₂_cpv : Tendsto (fun ε => ∫ t in γ.a..γ.b,
      cauchyPrincipalValueIntegrandOn S0 g₂ γ.toFun ε t) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε => ∫ t in γ.a..γ.b,
      cauchyPrincipalValueIntegrandOn S0 g γ.toFun ε t) (𝓝[>] 0) (𝓝 0) := by
  rw [show (0 : ℂ) = 0 + 0 from (add_zero 0).symm]
  apply Filter.Tendsto.congr' _ (h_g₁_cpv.add h_g₂_cpv)
  filter_upwards [self_mem_nhdsWithin] with ε (hε : (0 : ℝ) < ε)
  have h_pw_eq : ∀ t, cauchyPrincipalValueIntegrandOn S0 g γ.toFun ε t =
      cauchyPrincipalValueIntegrandOn S0 (fun z => g₁ z + g₂ z) γ.toFun ε t := by
    intro t; simp only [cauchyPrincipalValueIntegrandOn]
    split_ifs with h_near
    · rfl
    · push Not at h_near
      have hne : γ.toFun t ≠ s := fun heq => by
        have := h_near s hs; rw [heq, sub_self, norm_zero] at this; linarith
      congr 1; exact h_off_s (γ.toFun t) hne
  rw [show (fun t => cauchyPrincipalValueIntegrandOn S0 g γ.toFun ε t) =
      fun t => cauchyPrincipalValueIntegrandOn S0
        (fun z => g₁ z + g₂ z) γ.toFun ε t from funext h_pw_eq]
  rw [show (fun t => cauchyPrincipalValueIntegrandOn S0
        (fun z => g₁ z + g₂ z) γ.toFun ε t) =
      fun t => cauchyPrincipalValueIntegrandOn S0 g₁ γ.toFun ε t +
        cauchyPrincipalValueIntegrandOn S0 g₂ γ.toFun ε t from
    funext (fun t => cpvIntegrandOn_add S0 g₁ g₂ γ.toFun ε t)]
  exact (intervalIntegral.integral_add
    (intervalIntegrable_cpvIntegrandOn_of_continuousOn_diff U S0 g₁
      h_g₁_cont γ hγ_in_U ε hε)
    (intervalIntegrable_cpvIntegrandOn_of_continuousOn_diff U S0 g₂
      h_g₂_cont γ hγ_in_U ε hε)).symm

/-- A function that agrees with an analytic function near `s` and equals
`g₁ - g₂` away from `s` (where both are differentiable off `{s}`) is differentiable on `U`. -/
private theorem differentiableOn_of_eventuallyEq_analytic_off_sub
    (U : Set ℂ) (s : ℂ) (err_nf err_loc g₁ g₂ : ℂ → ℂ)
    (h_ev : err_nf =ᶠ[𝓝 s] err_loc)
    (h_err_loc_an : AnalyticAt ℂ err_loc s)
    (h_off_s : ∀ w, w ≠ s → err_nf w = g₁ w - g₂ w)
    (h_g₁_diff : DifferentiableOn ℂ g₁ ({s}ᶜ : Set ℂ))
    (h_g₂_diff : DifferentiableOn ℂ g₂ ({s}ᶜ : Set ℂ)) :
    DifferentiableOn ℂ err_nf U := by
  intro z _hz
  by_cases hzs : z = s
  · rw [hzs]
    exact ((h_ev.differentiableAt_iff (𝕜 := ℂ)).mpr
      h_err_loc_an.differentiableAt).differentiableWithinAt
  · have h_ev_z : err_nf =ᶠ[𝓝 z] fun w => g₁ w - g₂ w := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      exact ⟨{s}ᶜ, IsOpen.mem_nhds isOpen_compl_singleton
        (Set.mem_compl_singleton_iff.mpr hzs),
        fun w hw => h_off_s w (Set.mem_compl_singleton_iff.mp hw)⟩
    apply DifferentiableAt.differentiableWithinAt
    rw [h_ev_z.differentiableAt_iff]
    exact ((h_g₁_diff z (Set.mem_compl_singleton_iff.mpr hzs)).differentiableAt
        (isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr hzs))).sub
      ((h_g₂_diff z (Set.mem_compl_singleton_iff.mpr hzs)).differentiableAt
        (isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr hzs)))

/-- When N_s = 0, the Laurent expansion `f = g_loc + 0` means `f` is analytic at `s`,
so both the principal part and residue vanish, making the per-term function identically 0.
The CPV integral of the zero function trivially tends to 0. -/
private theorem cpv_perTerm_crossed_zero_order (S0 : Finset ℂ) (f : ℂ → ℂ)
    (γ : PiecewiseC1Immersion) (hMero_s : MeromorphicAt f s)
    (g_loc : ℂ → ℂ) (hg_loc_an : AnalyticAt ℂ g_loc s)
    (hf_eq_loc : ∀ᶠ z in 𝓝[≠] s,
      f z = g_loc z + ∑ k : Fin 0, (default : Fin 0 → ℂ) k / (z - s) ^ (k.val + 1)) :
    Tendsto (fun ε => ∫ t in γ.a..γ.b,
      cauchyPrincipalValueIntegrandOn S0
        (fun z => meromorphicPrincipalPart f s z - residueAt f s / (z - s))
        γ.toFun ε t)
      (𝓝[>] 0) (𝓝 0) := by
  have hf_tends : Tendsto f (𝓝[≠] s) (𝓝 (g_loc s)) := by
    apply Filter.Tendsto.congr'
    · filter_upwards [hf_eq_loc] with z hz
      simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero] at hz
      exact hz.symm
    · exact hg_loc_an.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h_ord_nn : 0 ≤ meromorphicOrderAt f s :=
    (tendsto_nhds_iff_meromorphicOrderAt_nonneg hMero_s).mp ⟨g_loc s, hf_tends⟩
  have h_pp_zero : meromorphicPrincipalPart f s = fun _ => 0 := by
    unfold meromorphicPrincipalPart
    exact dif_neg (fun h => absurd h.2 (not_lt.mpr h_ord_nn))
  have h_res_zero : residueAt f s = 0 := by
    have hf_eq_g : ∀ᶠ (z : ℂ) in 𝓝[≠] s, f z = g_loc z := by
      filter_upwards [hf_eq_loc] with z hz
      simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero] at hz
      exact hz
    exact residueAt_eq_zero_of_analyticExpansion f s g_loc hg_loc_an hf_eq_g
  have h_term_eq_zero : (fun z => meromorphicPrincipalPart f s z -
      residueAt f s / (z - s)) = fun _ => 0 := by
    ext z; simp only [h_pp_zero, h_res_zero]; simp [zero_div]
  rw [h_term_eq_zero]
  simp only [cauchyPrincipalValueIntegrandOn, zero_mul, ite_self]
  simp [intervalIntegral.integral_zero]

/-- When the curve does not cross `s`, the per-term CPV integral of
`pp_s - res_s/(z-s)` tends to 0: the term is continuous on the image, has
zero integral by the finset-vanishing hypothesis, so the CPV converges. -/
private theorem cpv_perTerm_uncrossed (U : Set ℂ) (S0 : Finset ℂ)
    (f : ℂ → ℂ) (γ : PiecewiseC1Immersion)
    (_hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hMero : ∀ s ∈ S0, MeromorphicAt f s) (hS0_in_U : ∀ s ∈ S0, s ∈ U)
    (h_finset_vanish : ∀ (T : Finset ℂ) (g : ℂ → ℂ),
      (∀ s ∈ T, MeromorphicAt g s) → (∀ s ∈ T, residueAt g s = 0) →
      DifferentiableOn ℂ g (U \ ↑T) → (∀ s ∈ T, s ∈ U) →
      (∀ s ∈ T, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) →
      ∫ t in γ.a..γ.b, g (γ.toFun t) * deriv γ.toFun t = 0)
    (s : ℂ) (hs : s ∈ S0)
    (h_avoids : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) :
    Tendsto (fun ε => ∫ t in γ.a..γ.b,
      cauchyPrincipalValueIntegrandOn S0
        (fun z => meromorphicPrincipalPart f s z - residueAt f s / (z - s))
        γ.toFun ε t)
      (𝓝[>] 0) (𝓝 0) := by
  set term_s : ℂ → ℂ := fun z =>
    meromorphicPrincipalPart f s z - residueAt f s / (z - s) with hterm_s_def
  have h_term_cont_image : ContinuousOn term_s (γ.toFun '' Icc γ.a γ.b) := by
    apply ContinuousOn.sub
    · exact (meromorphicPrincipalPart_differentiableOn f s
        (hMero s hs)).continuousOn.mono
        (fun z ⟨t, ht, htz⟩ =>
          Set.mem_compl_singleton_iff.mpr (htz ▸ h_avoids t ht))
    · apply ContinuousOn.div continuousOn_const
        (continuousOn_id.sub continuousOn_const)
      intro z ⟨t, ht, htz⟩
      exact sub_ne_zero.mpr (htz ▸ h_avoids t ht)
  have h_term_int_zero : ∫ t in γ.a..γ.b,
      term_s (γ.toFun t) * deriv γ.toFun t = 0 := by
    have h_term_diff : DifferentiableOn ℂ term_s (U \ {s}) :=
      (differentiableOn_ppMinusRes f s (hMero s hs)).mono
        (fun z hz => Set.mem_compl_singleton_iff.mpr hz.2)
    have h_term_mero : MeromorphicAt term_s s :=
      meromorphicAt_ppMinusRes f s (hMero s hs)
    have h_term_res : residueAt term_s s = 0 :=
      residueAt_ppMinusRes_eq_zero f s (hMero s hs)
    exact h_finset_vanish {s} term_s
      (fun s' hs' => by rw [Finset.mem_singleton.mp hs']; exact h_term_mero)
      (fun s' hs' => by rw [Finset.mem_singleton.mp hs']; exact h_term_res)
      (by rwa [Finset.coe_singleton])
      (fun s' hs' => by rw [Finset.mem_singleton.mp hs']; exact hS0_in_U s hs)
      (fun s' hs' t ht => by rw [Finset.mem_singleton.mp hs']; exact h_avoids t ht)
  exact tendsto_cpv_of_continuousOn_zero_integral S0 term_s γ
    h_term_cont_image h_term_int_zero

private theorem cpv_div_pow_eq_const_mul_zpow (S0 : Finset ℂ) (γ : PiecewiseC1Immersion)
    (c : ℂ) (s : ℂ) (m : ℕ) :
    (fun ε => ∫ t in γ.a..γ.b,
      cauchyPrincipalValueIntegrandOn S0
        (fun z => c / (z - s) ^ (m + 1)) γ.toFun ε t) =
    fun ε => c * ∫ t in γ.a..γ.b,
      cauchyPrincipalValueIntegrandOn S0
        (fun z => (z - s) ^ (-(↑(m + 1) : ℤ))) γ.toFun ε t := by
  ext ε; rw [show (fun t => cauchyPrincipalValueIntegrandOn S0
      (fun z => c / (z - s) ^ (m + 1)) γ.toFun ε t) =
    (fun t => c * cauchyPrincipalValueIntegrandOn S0
      (fun z => (z - s) ^ (-(↑(m + 1) : ℤ))) γ.toFun ε t) from
    funext fun t => by
      have : (fun z => c / (z - s) ^ (m + 1)) =
          fun z => c * (z - s) ^ (-(↑(m + 1) : ℤ)) := by
        ext z; rw [div_eq_mul_inv, zpow_neg, zpow_natCast, inv_eq_one_div, one_div]
      rw [this]; exact cpvIntegrandOn_const_smul S0 _ _ γ.toFun ε t]
  exact intervalIntegral.integral_const_mul _ _

private theorem cpv_polar_term_tendsto (S0 : Finset ℂ) (f : ℂ → ℂ)
    (γ : PiecewiseC1Immersion) (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (s : ℂ) (hs : s ∈ S0) (hMero_s : MeromorphicAt f s)
    {N_s : ℕ} (_hN_s_pos : 0 < N_s) (a_s : Fin N_s → ℂ)
    (g_loc : ℂ → ℂ) (hg_loc_an : AnalyticAt ℂ g_loc s)
    (hf_eq_loc : ∀ᶠ z in 𝓝[≠] s,
      f z = g_loc z + ∑ k : Fin N_s, a_s k / (z - s) ^ (k.val + 1))
    (t₁ : ℝ) (ht₁_Ioo : t₁ ∈ Ioo γ.a γ.b)
    (hcross₁ : γ.toFun t₁ = s)
    (h_unique_s : ∀ t ∈ Icc γ.a γ.b, γ.toFun t = s → t = t₁)
    (h_flat_s : IsFlatOfOrder γ.toFun t₁ (poleOrderAt f s))
    (h_angle : ∀ (k : Fin N_s), a_s k ≠ 0 → k.val ≥ 1 →
      ∃ n : ℤ, (↑k.val : ℝ) * _root_.angleAtCrossing γ t₁ ht₁_Ioo =
        ↑n * (2 * Real.pi))
    (k : Fin N_s) (hk_ge : k.val ≥ 1) :
    Tendsto (fun ε => ∫ t in γ.a..γ.b,
      cauchyPrincipalValueIntegrandOn S0
        (fun z => a_s k / (z - s) ^ (k.val + 1))
        γ.toFun ε t) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨kv, hkv⟩ := k; change kv ≥ 1 at hk_ge
  have hm : 2 ≤ kv + 1 := by omega
  by_cases ha_zero : a_s ⟨kv, hkv⟩ = 0
  · have h_zero : ∀ ε t, cauchyPrincipalValueIntegrandOn S0
        (fun z => a_s ⟨kv, hkv⟩ / (z - s) ^ (kv + 1))
        γ.toFun ε t = 0 := by
      intro ε t; simp only [cauchyPrincipalValueIntegrandOn, ha_zero,
        zero_div, zero_mul, ite_self]
    simp only [show (fun ε => ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0
          (fun z => a_s ⟨kv, hkv⟩ / (z - s) ^ (kv + 1))
          γ.toFun ε t) = fun _ => 0 from
      funext fun ε => by
        rw [show (fun t => cauchyPrincipalValueIntegrandOn S0
            (fun z => a_s ⟨kv, hkv⟩ / (z - s) ^ (kv + 1))
            γ.toFun ε t) = fun _ => 0 from funext (h_zero ε)]
        exact intervalIntegral.integral_zero]
    exact tendsto_const_nhds
  · have h_order_bound : kv + 1 ≤ poleOrderAt f s :=
      laurent_coeff_le_poleOrder f s hMero_s a_s g_loc hg_loc_an
        hf_eq_loc ha_zero
    have h_zpow := multipoint_pv_zpow_tendsto_zero S0 γ s (kv + 1) hm
      hs t₁ ht₁_Ioo hcross₁ h_unique_s hγ_closed
      (IsFlatOfOrder.of_le h_flat_s h_order_bound
        ((γ.continuous_toFun t₁ (Ioo_subset_Icc_self ht₁_Ioo)).continuousAt
          (Icc_mem_nhds ht₁_Ioo.1 ht₁_Ioo.2)))
      (by rw [show (kv + 1 - 1 : ℕ) = kv from by omega]
          exact h_angle ⟨kv, hkv⟩ ha_zero hk_ge)
    have h_eq := cpv_div_pow_eq_const_mul_zpow S0 γ (a_s ⟨kv, hkv⟩) s kv
    rw [h_eq, show (0 : ℂ) = a_s ⟨kv, hkv⟩ * 0 from (mul_zero _).symm]
    exact Filter.Tendsto.const_smul h_zpow (a_s ⟨kv, hkv⟩)

/-- Higher-order polar terms: `∑ k, (if k≥1 then aₖ/(z-s)^{k+1} else 0)`. -/
private noncomputable def assembly_polarHigher
    {N_s : ℕ} (a_s : Fin N_s → ℂ) (s : ℂ) : ℂ → ℂ :=
  fun z => ∑ k : Fin N_s, if k.val ≥ 1 then a_s k / (z - s) ^ (k.val + 1) else 0

/-- Error between the two analytic corrections: `g_loc - g_rp`. -/
private noncomputable def assembly_errLoc (g_loc g_rp : ℂ → ℂ) : ℂ → ℂ :=
  fun z => g_loc z - g_rp z

/-- Normalized error: equals `err_loc s` at `s`, equals `term_s - polarHigher` away from `s`. -/
private noncomputable def assembly_errNF (f : ℂ → ℂ) (s : ℂ)
    (g_loc g_rp : ℂ → ℂ) {N_s : ℕ} (a_s : Fin N_s → ℂ) : ℂ → ℂ :=
  fun z => if z = s then assembly_errLoc g_loc g_rp s
    else (meromorphicPrincipalPart f s z - residueAt f s / (z - s)) -
      assembly_polarHigher a_s s z

private theorem assembly_errNF_eventuallyEq (f : ℂ → ℂ) (s : ℂ)
    {N_s : ℕ} (hN_s_pos : 0 < N_s) (a_s : Fin N_s → ℂ) (g_loc g_rp : ℂ → ℂ)
    (hf_eq_loc : ∀ᶠ z in 𝓝[≠] s,
      f z = g_loc z + ∑ k : Fin N_s, a_s k / (z - s) ^ (k.val + 1))
    (hg_rp_eq : ∀ᶠ z in 𝓝[≠] s,
      f z - meromorphicPrincipalPart f s z = g_rp z)
    (h_a0_eq : a_s ⟨0, hN_s_pos⟩ = residueAt f s) :
    assembly_errNF f s g_loc g_rp a_s =ᶠ[𝓝 s] assembly_errLoc g_loc g_rp := by
  rw [Filter.eventuallyEq_iff_exists_mem]
  rw [Filter.Eventually, Metric.mem_nhdsWithin_iff] at hf_eq_loc hg_rp_eq
  obtain ⟨r1, hr1_pos, hr1_eq⟩ := hf_eq_loc
  obtain ⟨r2, hr2_pos, hr2_eq⟩ := hg_rp_eq
  set r := min r1 r2 with hr_def
  have hr_pos : 0 < r := lt_min hr1_pos hr2_pos
  refine ⟨Metric.ball s r, Metric.ball_mem_nhds s hr_pos, fun z hz => ?_⟩
  by_cases hzs : z = s
  · subst hzs; simp [assembly_errNF]
  · simp only [assembly_errNF, if_neg hzs, assembly_polarHigher, assembly_errLoc]
    have hz_in_1 : z ∈ Metric.ball s r1 ∩ {s}ᶜ :=
      ⟨Metric.mem_ball.mpr ((Metric.mem_ball.mp hz).trans_le (min_le_left _ _)),
       Set.mem_compl_singleton_iff.mpr hzs⟩
    have hz_in_2 : z ∈ Metric.ball s r2 ∩ {s}ᶜ :=
      ⟨Metric.mem_ball.mpr ((Metric.mem_ball.mp hz).trans_le (min_le_right _ _)),
       Set.mem_compl_singleton_iff.mpr hzs⟩
    have hfz : f z = g_loc z + ∑ k : Fin N_s,
        a_s k / (z - s) ^ (k.val + 1) := hr1_eq hz_in_1
    have hgrpz : f z - meromorphicPrincipalPart f s z = g_rp z :=
      hr2_eq hz_in_2
    have hpp : meromorphicPrincipalPart f s z = f z - g_rp z := by
      linear_combination -hgrpz
    rw [hpp, hfz]
    have h_sum_split : ∑ k : Fin N_s, a_s k / (z - s) ^ (k.val + 1) -
        ∑ k : Fin N_s, (if k.val ≥ 1 then a_s k / (z - s) ^ (k.val + 1) else 0) =
        a_s ⟨0, hN_s_pos⟩ / (z - s) := by
      rw [← Finset.sum_sub_distrib]
      rw [Finset.sum_eq_single ⟨0, hN_s_pos⟩]
      · simp only [zero_add, pow_one, ge_iff_le, nonpos_iff_eq_zero, one_ne_zero, ↓reduceIte,
        sub_zero]
      · intro k _ hk
        have hkval : k.val ≥ 1 := by
          by_contra h
          push Not at h
          have : k.val = 0 := by omega
          exact hk (Fin.ext this)
        simp only [hkval, if_true, sub_self]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [h_a0_eq] at h_sum_split
    linear_combination h_sum_split

private theorem assembly_polarHigher_differentiableOn
    {N_s : ℕ} (a_s : Fin N_s → ℂ) (s : ℂ) :
    DifferentiableOn ℂ (assembly_polarHigher a_s s) ({s}ᶜ : Set ℂ) := by
  intro z hzs'
  have hzs : z ≠ s := Set.mem_compl_singleton_iff.mp hzs'
  have h_each : ∀ k : Fin N_s, DifferentiableAt ℂ
      (fun w => if k.val ≥ 1 then a_s k / (w - s) ^ (k.val + 1) else 0) z := by
    intro k
    by_cases hk : k.val ≥ 1
    · simp only [hk, ite_true]
      exact (differentiableAt_const _).div
        ((differentiableAt_id.sub (differentiableAt_const _)).pow _)
        (pow_ne_zero _ (sub_ne_zero.mpr hzs))
    · simp only [hk, ite_false]; exact differentiableAt_const 0
  change DifferentiableWithinAt ℂ (fun w => ∑ k : Fin N_s,
    if k.val ≥ 1 then a_s k / (w - s) ^ (k.val + 1) else 0) _ z
  have h_eq_sum : (fun w => ∑ k : Fin N_s,
      if k.val ≥ 1 then a_s k / (w - s) ^ (k.val + 1) else 0) =
    ∑ k : Fin N_s, fun w =>
      if k.val ≥ 1 then a_s k / (w - s) ^ (k.val + 1) else 0 := by
    ext w; simp [Finset.sum_apply]
  rw [h_eq_sum]
  exact (DifferentiableAt.sum fun k _ => h_each k).differentiableWithinAt

private theorem cpv_polarHigher_tendsto (U : Set ℂ) (S0 : Finset ℂ)
    (_f : ℂ → ℂ) (γ : PiecewiseC1Immersion)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (s : ℂ) (hs : s ∈ S0) {N_s : ℕ} (a_s : Fin N_s → ℂ)
    (h_polar_term_tendsto : ∀ (k : Fin N_s), k.val ≥ 1 →
      Tendsto (fun ε => ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0
          (fun z => a_s k / (z - s) ^ (k.val + 1))
          γ.toFun ε t) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε => ∫ t in γ.a..γ.b,
      cauchyPrincipalValueIntegrandOn S0 (assembly_polarHigher a_s s) γ.toFun ε t)
    (𝓝[>] 0) (𝓝 0) :=
  cpv_tendsto_zero_of_fin_sum S0 γ U hγ_in_U
    (fun k z => if k.val ≥ 1 then a_s k / (z - s) ^ (k.val + 1) else 0)
    (fun k => by
      by_cases hk : k.val ≥ 1
      · simp only [hk, ite_true]
        apply ContinuousOn.div continuousOn_const
          ((continuousOn_id.sub continuousOn_const).pow _)
        intro z ⟨_, hz_not_S0⟩
        exact pow_ne_zero _ (sub_ne_zero.mpr
          (fun heq => by subst heq; exact hz_not_S0 (Finset.mem_coe.mpr hs)))
      · simp only [hk, ite_false]; exact continuousOn_const)
    (fun k => by
      by_cases hk : k.val ≥ 1
      · have h_eq : (fun z => if k.val ≥ 1 then
            a_s k / (z - s) ^ (k.val + 1) else 0) =
          fun z => a_s k / (z - s) ^ (k.val + 1) := by ext z; simp [hk]
        simp_rw [h_eq]; exact h_polar_term_tendsto k hk
      · have h_eq : (fun z => if k.val ≥ 1 then
            a_s k / (z - s) ^ (k.val + 1) else 0) =
          fun _ => (0 : ℂ) := by ext z; simp [hk]
        simp_rw [h_eq, cauchyPrincipalValueIntegrandOn, zero_mul, ite_self,
          intervalIntegral.integral_zero]
        exact tendsto_const_nhds)

private theorem cpv_perTerm_crossed_positive_order
    (U : Set ℂ) (S0 : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Immersion)
    (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hMero : ∀ s ∈ S0, MeromorphicAt f s)
    (hCondA : SatisfiesConditionA' γ S0 (fun s => poleOrderAt f s))
    (h_unique_cross : ∀ s ∈ S0, ∀ t₁ ∈ Icc γ.a γ.b, ∀ t₂ ∈ Icc γ.a γ.b,
      γ.toFun t₁ = s → γ.toFun t₂ = s → t₁ = t₂)
    (h_holo_vanish : ∀ g : ℂ → ℂ, DifferentiableOn ℂ g U →
      ∫ t in γ.a..γ.b, g (γ.toFun t) * deriv γ.toFun t = 0)
    (s : ℂ) (hs : s ∈ S0)
    {N_s : ℕ} (hN_s_pos : 0 < N_s) (a_s : Fin N_s → ℂ)
    (g_loc : ℂ → ℂ) (hg_loc_an : AnalyticAt ℂ g_loc s)
    (hf_eq_loc : ∀ᶠ z in 𝓝[≠] s,
      f z = g_loc z + ∑ k : Fin N_s, a_s k / (z - s) ^ (k.val + 1))
    (t₁ : ℝ) (ht₁ : t₁ ∈ Icc γ.a γ.b) (ht₁_Ioo : t₁ ∈ Ioo γ.a γ.b)
    (hcross₁ : γ.toFun t₁ = s)
    (h_angle : ∀ (k : Fin N_s), a_s k ≠ 0 → k.val ≥ 1 →
      ∃ n : ℤ, (↑k.val : ℝ) * _root_.angleAtCrossing γ t₁ ht₁_Ioo =
        ↑n * (2 * Real.pi)) :
    Tendsto (fun ε => ∫ t in γ.a..γ.b,
      cauchyPrincipalValueIntegrandOn S0
        (fun z => meromorphicPrincipalPart f s z - residueAt f s / (z - s))
        γ.toFun ε t)
      (𝓝[>] 0) (𝓝 0) := by
  set term_s := fun z => meromorphicPrincipalPart f s z - residueAt f s / (z - s) with hterm_s
  have h_unique_s := fun t ht hc => h_unique_cross s hs t ht t₁ ht₁ hc hcross₁
  have h_a0 := (residueAt_eq_laurent_head_coeff f s N_s hN_s_pos a_s g_loc hg_loc_an hf_eq_loc).symm
  obtain ⟨g_rp, hg_rp_an, hg_rp_eq⟩ :=
    meromorphicAt_sub_principalPart_eventually f s (hMero s hs)
  let err_nf := assembly_errNF f s g_loc g_rp a_s
  have hD : DifferentiableOn ℂ err_nf U :=
    differentiableOn_of_eventuallyEq_analytic_off_sub U s err_nf (assembly_errLoc g_loc g_rp)
      term_s (assembly_polarHigher a_s s)
      (assembly_errNF_eventuallyEq f s hN_s_pos a_s g_loc g_rp hf_eq_loc hg_rp_eq h_a0)
      (hg_loc_an.sub hg_rp_an) (fun w hw => by
        change assembly_errNF f s g_loc g_rp a_s w = term_s w - _
        simp only [assembly_errNF, if_neg hw, assembly_polarHigher, hterm_s])
      (differentiableOn_ppMinusRes f s (hMero s hs)) (assembly_polarHigher_differentiableOn a_s s)
  exact cpv_tendsto_zero_of_add_split U S0 γ hγ_in_U term_s err_nf
    (assembly_polarHigher a_s s) s hs (fun z hz => by
      simp only [err_nf, assembly_errNF, if_neg hz, assembly_polarHigher]; ring)
    (hD.continuousOn.mono Set.diff_subset)
    ((assembly_polarHigher_differentiableOn a_s s).continuousOn.mono fun z ⟨_, hz⟩ =>
      Set.mem_compl_singleton_iff.mpr fun heq => hz (Finset.mem_coe.mpr (heq ▸ hs)))
    (tendsto_cpv_of_continuousOn_zero_integral S0 err_nf γ
      (hD.continuousOn.mono fun z ⟨t, ht, htz⟩ =>
        htz ▸ hγ_in_U t ht) (h_holo_vanish err_nf hD))
    (cpv_polarHigher_tendsto U S0 f γ hγ_in_U s hs a_s fun k hk =>
      cpv_polar_term_tendsto S0 f γ hγ_closed s hs (hMero s hs) hN_s_pos a_s g_loc hg_loc_an
        hf_eq_loc t₁ ht₁_Ioo hcross₁ h_unique_s
          (hCondA s hs t₁ ht₁ hcross₁ ht₁_Ioo) h_angle k hk)

private theorem assembly_ppMinusRes_continuousOn (S0 : Finset ℂ) (f : ℂ → ℂ) (U : Set ℂ)
    (hMero : ∀ s ∈ S0, MeromorphicAt f s) (s : ℂ) (hs : s ∈ S0) :
    ContinuousOn (fun z => meromorphicPrincipalPart f s z - residueAt f s / (z - s))
      (U \ ↑S0) := by
  apply ContinuousOn.sub
  · exact (meromorphicPrincipalPart_differentiableOn f s (hMero s hs)).continuousOn.mono
      (fun z hz => Set.mem_compl_singleton_iff.mpr
        (fun heq => by subst heq; exact hz.2 (Finset.mem_coe.mpr hs)))
  · apply ContinuousOn.div continuousOn_const (continuousOn_id.sub continuousOn_const)
    intro z ⟨_, hz_not_S0⟩
    exact sub_ne_zero.mpr (fun heq => by
      subst heq; exact hz_not_S0 (Finset.mem_coe.mpr hs))

private theorem cpv_perTerm_dispatch (U : Set ℂ) (S0 : Finset ℂ)
    (f : ℂ → ℂ) (γ : PiecewiseC1Immersion)
    (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hMero : ∀ s ∈ S0, MeromorphicAt f s)
    (hCondA : SatisfiesConditionA' γ S0 (fun s => poleOrderAt f s))
    (hCondB : SatisfiesConditionB γ f S0)
    (hS0_in_U : ∀ s ∈ S0, s ∈ U)
    (h_unique_cross : ∀ s ∈ S0, ∀ t₁ ∈ Icc γ.a γ.b, ∀ t₂ ∈ Icc γ.a γ.b,
      γ.toFun t₁ = s → γ.toFun t₂ = s → t₁ = t₂)
    (h_holo_vanish : ∀ g : ℂ → ℂ, DifferentiableOn ℂ g U →
      ∫ t in γ.a..γ.b, g (γ.toFun t) * deriv γ.toFun t = 0)
    (h_finset_vanish : ∀ (T : Finset ℂ) (g : ℂ → ℂ),
      (∀ s ∈ T, MeromorphicAt g s) → (∀ s ∈ T, residueAt g s = 0) →
      DifferentiableOn ℂ g (U \ ↑T) → (∀ s ∈ T, s ∈ U) →
      (∀ s ∈ T, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) →
      ∫ t in γ.a..γ.b, g (γ.toFun t) * deriv γ.toFun t = 0)
    (h_crossed_in_Ioo : ∀ s ∈ S0, ∀ t ∈ Icc γ.a γ.b, γ.toFun t = s →
      t ∈ Ioo γ.a γ.b)
    (s : ℂ) (hs : s ∈ S0) :
    Tendsto (fun ε => ∫ t in γ.a..γ.b,
      cauchyPrincipalValueIntegrandOn S0
        (fun z => meromorphicPrincipalPart f s z - residueAt f s / (z - s))
        γ.toFun ε t) (𝓝[>] 0) (𝓝 0) := by
  by_cases h_crossed : ∃ t ∈ Icc γ.a γ.b, γ.toFun t = s
  · obtain ⟨t₁, ht₁, hcross₁⟩ := h_crossed
    have ht₁_Ioo := h_crossed_in_Ioo s hs t₁ ht₁ hcross₁
    obtain ⟨N_s, a_s, g_loc, hg_loc_an, hf_eq_loc, h_angle⟩ :=
      hCondB.laurent_compatible s hs t₁ ht₁ hcross₁ ht₁_Ioo
    rcases Nat.eq_zero_or_pos N_s with hN_s_zero | hN_s_pos
    · subst hN_s_zero
      exact cpv_perTerm_crossed_zero_order S0 f γ (hMero s hs)
        g_loc hg_loc_an hf_eq_loc
    · exact cpv_perTerm_crossed_positive_order U S0 f γ hγ_closed
        hγ_in_U hMero hCondA h_unique_cross h_holo_vanish s hs hN_s_pos
        a_s g_loc hg_loc_an hf_eq_loc t₁ ht₁ ht₁_Ioo hcross₁ h_angle
  · push Not at h_crossed
    exact cpv_perTerm_uncrossed U S0 f γ hγ_in_U hMero hS0_in_U h_finset_vanish
      s hs (fun t ht => h_crossed t ht)

private theorem assembly_abstract_crossings_case (U : Set ℂ) (hU : IsOpen U)
    (S0 : Finset ℂ) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ S0))
    (γ : PiecewiseC1Immersion) (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hMero : ∀ s ∈ S0, MeromorphicAt f s)
    (hCondA : SatisfiesConditionA' γ S0 (fun s => poleOrderAt f s))
    (hCondB : SatisfiesConditionB γ f S0)
    (h_no_endpt : ∀ s ∈ S0, γ.toFun γ.a ≠ s ∧ γ.toFun γ.b ≠ s)
    (h_unique_cross : ∀ s ∈ S0, ∀ t₁ ∈ Icc γ.a γ.b, ∀ t₂ ∈ Icc γ.a γ.b,
      γ.toFun t₁ = s → γ.toFun t₂ = s → t₁ = t₂)
    (hS0_in_U : ∀ s ∈ S0, s ∈ U)
    (h_holo_vanish : ∀ g : ℂ → ℂ, DifferentiableOn ℂ g U →
      ∫ t in γ.a..γ.b, g (γ.toFun t) * deriv γ.toFun t = 0)
    (h_finset_vanish : ∀ (T : Finset ℂ) (g : ℂ → ℂ),
      (∀ s ∈ T, MeromorphicAt g s) → (∀ s ∈ T, residueAt g s = 0) →
      DifferentiableOn ℂ g (U \ ↑T) → (∀ s ∈ T, s ∈ U) →
      (∀ s ∈ T, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) →
      ∫ t in γ.a..γ.b, g (γ.toFun t) * deriv γ.toFun t = 0)
    (h : ℂ → ℂ) (hh_eq : h = fun z => f z - ∑ s ∈ S0, residueAt f s / (z - s)) :
    Tendsto (fun ε => ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0 h γ.toFun ε t)
      (𝓝[>] 0) (𝓝 0) := by
  have h_crossed_in_Ioo : ∀ s ∈ S0, ∀ t ∈ Icc γ.a γ.b, γ.toFun t = s →
      t ∈ Ioo γ.a γ.b := fun s hs t ht hcross =>
    ⟨ht.1.lt_or_eq.elim id fun h => absurd (h ▸ hcross) (h_no_endpt s hs).1,
     ht.2.lt_or_eq.elim id fun h => absurd (h ▸ hcross) (h_no_endpt s hs).2⟩
  choose g_corr hg_corr_an hg_corr_eq using
    fun s (hs : s ∈ S0) => meromorphicAt_sub_principalPart_eventually f s (hMero s hs)
  let h_reg_nf : ℂ → ℂ := assembly_regNF S0 f g_corr
  have h_reg_nf_diff_U : DifferentiableOn ℂ h_reg_nf U :=
    assembly_regNF_differentiableOn S0 f hU hf hMero g_corr hg_corr_an hg_corr_eq
  have h_fun_eq_off_S0 : ∀ z, z ∉ (↑S0 : Set ℂ) →
      h z = h_reg_nf z + assembly_pol S0 f z := by
    intro z hz_not_S0
    have hz_not_S : z ∉ S0 := fun hh => hz_not_S0 (Finset.mem_coe.mpr hh)
    change h z = (if _ : z ∈ S0 then _ else assembly_reg S0 f z) + assembly_pol S0 f z
    rw [dif_neg hz_not_S]
    simp only [hh_eq, assembly_reg, assembly_pol, assembly_totalPP, Finset.sum_sub_distrib]; ring
  exact cpv_tendsto_zero_of_add_split_set U S0 γ hγ_in_U h h_reg_nf (assembly_pol S0 f)
    h_fun_eq_off_S0 (h_reg_nf_diff_U.continuousOn.mono Set.diff_subset)
    (continuousOn_finsetSum _ fun s hs => assembly_ppMinusRes_continuousOn S0 f U hMero s hs)
    (tendsto_cpv_of_continuousOn_zero_integral S0 h_reg_nf γ
      (h_reg_nf_diff_U.continuousOn.mono fun z ⟨t, ht, htz⟩ => htz ▸ hγ_in_U t ht)
      (h_holo_vanish h_reg_nf h_reg_nf_diff_U))
    (cpv_tendsto_zero_of_finset_sum S0 γ U hγ_in_U
      (fun s z => meromorphicPrincipalPart f s z - residueAt f s / (z - s))
      (fun s hs => assembly_ppMinusRes_continuousOn S0 f U hMero s hs)
      fun s hs => cpv_perTerm_dispatch U S0 f γ hγ_closed hγ_in_U hMero hCondA
        hCondB hS0_in_U h_unique_cross h_holo_vanish h_finset_vanish h_crossed_in_Ioo s hs)

private theorem meromorphicAt_f_sub_residueSum (S0 : Finset ℂ) (f : ℂ → ℂ)
    (hMero : ∀ s ∈ S0, MeromorphicAt f s) (s : ℂ) (hs : s ∈ S0) :
    MeromorphicAt (fun z => f z - ∑ s' ∈ S0, residueAt f s' / (z - s')) s := by
  apply MeromorphicAt.fun_sub (hMero s hs)
  suffices ∀ (T : Finset ℂ),
      MeromorphicAt (fun z => ∑ s' ∈ T, residueAt f s' / (z - s')) s from this S0
  intro T
  induction T using Finset.induction with
  | empty => simp only [Finset.sum_empty]; exact MeromorphicAt.const 0 s
  | insert a T' ha' ih =>
    have h_eq : (fun z => ∑ s' ∈ insert a T', residueAt f s' / (z - s')) =
        (fun z => residueAt f a / (z - a) + ∑ s' ∈ T', residueAt f s' / (z - s')) := by
      ext z; exact Finset.sum_insert ha'
    rw [h_eq]
    exact ((MeromorphicAt.const (residueAt f a) s).fun_div
      ((MeromorphicAt.id s).fun_sub (MeromorphicAt.const a s))).fun_add ih

theorem higherOrderCancel_assembly_abstract (U : Set ℂ) (hU : IsOpen U)
    (S0 : Finset ℂ) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ S0))
    (γ : PiecewiseC1Immersion) (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hMero : ∀ s ∈ S0, MeromorphicAt f s)
    (hCondA : SatisfiesConditionA' γ S0 (fun s => poleOrderAt f s))
    (hCondB : SatisfiesConditionB γ f S0) (_hγ_meas : Measurable γ.toFun)
    (h_no_endpt : ∀ s ∈ S0, γ.toFun γ.a ≠ s ∧ γ.toFun γ.b ≠ s)
    (h_unique_cross : ∀ s ∈ S0, ∀ t₁ ∈ Icc γ.a γ.b, ∀ t₂ ∈ Icc γ.a γ.b,
      γ.toFun t₁ = s → γ.toFun t₂ = s → t₁ = t₂)
    (hS0_in_U : ∀ s ∈ S0, s ∈ U)
    (h_holo_vanish : ∀ g : ℂ → ℂ, DifferentiableOn ℂ g U →
      ∫ t in γ.a..γ.b, g (γ.toFun t) * deriv γ.toFun t = 0)
    (h_finset_vanish : ∀ (T : Finset ℂ) (g : ℂ → ℂ),
      (∀ s ∈ T, MeromorphicAt g s) → (∀ s ∈ T, residueAt g s = 0) →
      DifferentiableOn ℂ g (U \ ↑T) → (∀ s ∈ T, s ∈ U) →
      (∀ s ∈ T, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) →
      ∫ t in γ.a..γ.b, g (γ.toFun t) * deriv γ.toFun t = 0) :
    let h : ℂ → ℂ := fun z => f z - ∑ s ∈ S0, residueAt f s / (z - s)
    Tendsto (fun ε => ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0 h γ.toFun ε t)
      (𝓝[>] 0) (𝓝 0) := by
  intro h
  have hfres_diff : DifferentiableOn ℂ
      (fun z => ∑ s ∈ S0, residueAt f s / (z - s)) (U \ ↑S0) := by
    have h_eq : (fun z => ∑ s ∈ S0, residueAt f s / (z - s)) =
        (∑ s ∈ S0, fun z => residueAt f s / (z - s)) := funext fun z => by
      simp only [Finset.sum_apply]
    rw [h_eq]; exact DifferentiableOn.sum fun s _ =>
      DifferentiableOn.div (differentiableOn_const _)
        (differentiableOn_id.sub (differentiableOn_const _)) fun z ⟨_, hz⟩ =>
        sub_ne_zero.mpr fun heq => by subst heq; exact hz (Finset.mem_coe.mpr ‹_›)
  have hh_diff : DifferentiableOn ℂ h (U \ ↑S0) := hf.sub hfres_diff
  by_cases h_no_crossings : ∀ s ∈ S0, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s
  · exact tendsto_cpv_of_continuousOn_zero_integral S0 h γ
      (hh_diff.continuousOn.mono fun z ⟨t, ht, htz⟩ => htz ▸
        ⟨hγ_in_U t ht, fun hz => h_no_crossings _ (Finset.mem_coe.mp hz) t ht rfl⟩)
      (h_finset_vanish S0 h (fun s hs => meromorphicAt_f_sub_residueSum S0 f hMero s hs)
        (fun s hs => residueAt_sub_residueSum_eq_zero S0 f s hs (hMero s hs))
        hh_diff hS0_in_U h_no_crossings)
  · exact assembly_abstract_crossings_case U hU S0 f hf γ hγ_closed hγ_in_U
      hMero hCondA hCondB h_no_endpt h_unique_cross hS0_in_U h_holo_vanish
      h_finset_vanish h rfl

end GeneralizedResidueTheory
