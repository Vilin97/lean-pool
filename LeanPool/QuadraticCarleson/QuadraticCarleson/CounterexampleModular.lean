/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.Counterexample

/-!
# Modular smallness of the counterexample

This file proves the `o(N)` modular bound in equation `eq:modularcalc` of
the paper for the existing counterexample family. Convexity gives the
secant estimate `∫ Φ(g) ≤ Φ(M) / M * ∫ g` whenever `0 ≤ g ≤ M`.
The packet family has mass `N` and admits the uniform envelope
`exp(C + N²)`, whose paper double logarithm is `O(log N)`. The assumed
strictly subendpoint growth of the Young function then yields the exact
claimed modular little-o bound.
-/

open MeasureTheory Set Filter Asymptotics
open scoped Topology

namespace QuadraticCarleson

theorem YoungFunction.nonneg (Φ : YoungFunction) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ Φ t := by
  simpa only [Φ.map_zero] using
    Φ.strictMonoOn_nonneg.monotoneOn (show (0 : ℝ) ∈ Ici 0 by simp) ht ht

/-- Convexity and the normalization at zero bound a Young function below
its secant through any positive endpoint. -/
theorem YoungFunction.le_secant (Φ : YoungFunction) {t M : ℝ}
    (ht : 0 ≤ t) (htM : t ≤ M) (hM : 0 < M) :
    Φ t ≤ (Φ M / M) * t := by
  have hb : 0 ≤ t / M := div_nonneg ht hM.le
  have ha : 0 ≤ 1 - t / M := sub_nonneg.mpr ((div_le_one₀ hM).mpr htM)
  have h := Φ.convexOn_nonneg.2 (show (0 : ℝ) ∈ Ici 0 by simp) hM.le ha hb
    (show 1 - t / M + t / M = 1 by ring)
  have heq : (1 - t / M) • (0 : ℝ) + (t / M) • M = t := by
    simp [smul_eq_mul, hM.ne']
  rw [heq, Φ.map_zero] at h
  simp only [smul_eq_mul, mul_zero, zero_add] at h
  calc
    Φ t ≤ (t / M) * Φ M := h
    _ = (Φ M / M) * t := by ring

/-- A useful modular estimate for nonnegative, bounded, compactly
supported continuous functions. -/
theorem YoungFunction.integral_le_secant (Φ : YoungFunction) {g : ℝ → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgn : ∀ x, 0 ≤ g x)
    {M : ℝ} (hM : 0 < M) (hgM : ∀ x, g x ≤ M) :
    (∫ x : ℝ, Φ (g x)) ≤ (Φ M / M) * ∫ x : ℝ, g x := by
  have hc : Continuous (fun x ↦ Φ (g x)) :=
    Φ.continuousOn_nonneg.comp_continuous hg (fun x ↦ hgn x)
  have hs : HasCompactSupport (fun x ↦ Φ (g x)) := hgc.comp_left Φ.map_zero
  have hi : Integrable g := hg.integrable_of_hasCompactSupport hgc
  calc
    (∫ x : ℝ, Φ (g x)) ≤ ∫ x : ℝ, (Φ M / M) * g x :=
      integral_mono (hc.integrable_of_hasCompactSupport hs) (hi.const_mul _)
        (fun x ↦ Φ.le_secant (hgn x) (hgM x) hM)
    _ = (Φ M / M) * ∫ x : ℝ, g x := integral_const_mul _ _

theorem packetSum_nonneg (N : ℕ) (x : ℝ) : 0 ≤ packetSum N x := by
  rw [packetSum, Finset.sum_apply]
  exact Finset.sum_nonneg (fun j _ ↦ wavePacket_nonneg _ _ (packetScale_pos N j))

theorem packetScale_inv (N j : ℕ) : (packetScale N j)⁻¹ = (2 : ℝ) ^ (N * j) := by
  simp only [packetScale, zpow_neg, inv_inv, zpow_natCast]

theorem packetSum_le_uniform {C : ℝ} (hC : 0 < C) (hbound : ∀ x, baseBump x ≤ C)
    {N : ℕ} (hN : 0 < N) (x : ℝ) : packetSum N x ≤ C * (2 : ℝ) ^ (N * N) := by
  rcases packetSum_eq_zero_or_eq_wavePacket hN x with hx | ⟨j, hj, hx⟩
  · rw [hx]
    positivity
  · rw [hx]
    calc
      wavePacket (j : ℝ) (packetScale N j) x ≤ (packetScale N j)⁻¹ * C :=
        wavePacket_le_of_baseBump_bound hbound _ _ (packetScale_pos N j)
      _ ≤ (2 : ℝ) ^ (N * N) * C := by
        rw [packetScale_inv]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left N (Finset.mem_Icc.mp hj).2))
          hC.le
      _ = C * (2 : ℝ) ^ (N * N) := mul_comm _ _

theorem packetSum_integral (N : ℕ) : (∫ x : ℝ, packetSum N x) = (N : ℝ) := by
  have hpacket : ∀ j : ℕ, (∫ x : ℝ, wavePacket (j : ℝ) (packetScale N j) x) = 1 :=
    fun j ↦ wavePacket_integral (j : ℝ) (packetScale_pos N j)
  rw [packetSum, Finset.sum_fn]
  rw [integral_finsetSum (Finset.Icc 1 N) (fun j _ ↦
    wavePacket_integrable (j : ℝ) (packetScale_pos N j))]
  simp_rw [hpacket]
  simp

/-- The modular expression in equation `eq:modularcalc` of the paper. -/
noncomputable def counterexampleModular (Φ : YoungFunction) (N : ℕ) : ℝ :=
  ∫ x : ℝ, Φ ((N : ℝ) * ‖counterexample N x‖ / Real.log (N : ℝ))

theorem scaled_counterexample_eq_packetSum {N : ℕ} (hN : 0 < N) (x : ℝ) :
    (N : ℝ) * ‖counterexample N x‖ / Real.log (N : ℝ) =
      packetSum N x / Real.log (N : ℝ) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [counterexample, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (counterexampleReal_nonneg N x), counterexampleReal]
  simp [hNr]

theorem counterexampleModular_eq {N : ℕ} (hN : 0 < N) (Φ : YoungFunction) :
    counterexampleModular Φ N =
      ∫ x : ℝ, Φ (packetSum N x / Real.log (N : ℝ)) := by
  simp only [counterexampleModular, scaled_counterexample_eq_packetSum hN]

theorem integrable_counterexampleModular_integrand (Φ : YoungFunction)
    {N : ℕ} (hN : 0 < N) (hlog : 0 ≤ Real.log (N : ℝ)) :
    Integrable (fun x : ℝ ↦
      Φ ((N : ℝ) * ‖counterexample N x‖ / Real.log (N : ℝ))) := by
  simp only [scaled_counterexample_eq_packetSum hN]
  have hc : Continuous (fun x ↦ packetSum N x / Real.log (N : ℝ)) :=
    (continuous_packetSum N).div_const _
  have hs : HasCompactSupport (fun x ↦ packetSum N x / Real.log (N : ℝ)) := by
    simp only [div_eq_mul_inv]
    exact (packetSum_hasCompactSupport N).mul_right
  exact (Φ.continuousOn_nonneg.comp_continuous hc
    (fun x ↦ div_nonneg (packetSum_nonneg N x) hlog)).integrable_of_hasCompactSupport
      (hs.comp_left Φ.map_zero)

theorem paperLog_nonneg (n : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ paperLog n t := by
  induction n with
  | zero => exact ht
  | succ n hn =>
    rw [paperLog_succ]
    exact Real.log_nonneg (by linarith)

/-- A convenient exponential envelope for the largest packet amplitude. -/
theorem packetSum_le_exp {C : ℝ} (hC : 0 < C) (hbound : ∀ x, baseBump x ≤ C)
    {N : ℕ} (hN : 0 < N) (x : ℝ) :
    packetSum N x ≤ Real.exp (C + (N : ℝ) ^ 2) := by
  apply (packetSum_le_uniform hC hbound hN x).trans
  calc
    C * (2 : ℝ) ^ (N * N) ≤ Real.exp C * (Real.exp 1) ^ (N * N) := by
      apply mul_le_mul (by linarith [Real.add_one_le_exp C] : C ≤ Real.exp C)
        (pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)]) _)
        (by positivity) (by positivity)
    _ = Real.exp (C + (N : ℝ) ^ 2) := by
      rw [← Real.exp_nat_mul, mul_one, ← Real.exp_add]
      congr 1
      push_cast
      ring

/-- The double logarithm of the exponential packet envelope is uniformly
bounded by a fixed multiple of `log N`. -/
theorem paperLog_two_exp_sq_le {C x : ℝ} (hC : 0 ≤ C) (hx : 1 ≤ x)
    (hlog : 1 ≤ Real.log x) :
    paperLog 2 (Real.exp (C + x ^ 2)) ≤ (C + 22) * Real.log x := by
  have hq : 0 ≤ C + x ^ 2 := by positivity
  have he : 1 ≤ Real.exp (C + x ^ 2) := Real.one_le_exp_iff.mpr hq
  have hinner : Real.log (10 + Real.exp (C + x ^ 2)) ≤
      Real.log 11 + C + x ^ 2 := by
    calc
      Real.log (10 + Real.exp (C + x ^ 2)) ≤
          Real.log (11 * Real.exp (C + x ^ 2)) :=
        Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 11 + C + x ^ 2 := by
        rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
        ring
  have hl11 : Real.log 11 ≤ 10 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 11 by norm_num)
    linarith
  have hinnerNonneg : 0 ≤ Real.log (10 + Real.exp (C + x ^ 2)) :=
    Real.log_nonneg (by linarith)
  have hxsq : 1 ≤ x ^ 2 := by nlinarith
  have hprod : (C + 20) ≤ (C + 20) * x ^ 2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ C + 20) (sub_nonneg.mpr hxsq)]
  have hout : 10 + Real.log (10 + Real.exp (C + x ^ 2)) ≤ (C + 21) * x ^ 2 := by
    nlinarith
  have hlC := Real.log_le_sub_one_of_pos (show 0 < C + 21 by positivity)
  calc
    paperLog 2 (Real.exp (C + x ^ 2)) =
        Real.log (10 + Real.log (10 + Real.exp (C + x ^ 2))) := rfl
    _ ≤ Real.log ((C + 21) * x ^ 2) := Real.log_le_log (by linarith) hout
    _ = Real.log (C + 21) + 2 * Real.log x := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
      norm_num
    _ ≤ (C + 22) * Real.log x := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ C + 20) (sub_nonneg.mpr hlog)]

theorem paperLog_two_exp_sq_isBigO (C : ℝ) (hC : 0 ≤ C) :
    (fun N : ℕ ↦ paperLog 2 (Real.exp (C + (N : ℝ) ^ 2))) =O[atTop]
      (fun N : ℕ ↦ Real.log (N : ℝ)) := by
  apply IsBigO.of_bound (C + 22)
  have hcast : Tendsto (fun N : ℕ ↦ (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hcast.eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp hcast).eventually_ge_atTop 1] with N hN hlog
  change 1 ≤ Real.log (N : ℝ) at hlog
  rw [Real.norm_eq_abs, abs_of_nonneg (paperLog_nonneg 2 (Real.exp_nonneg _)),
    Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ Real.log (N : ℝ))]
  exact paperLog_two_exp_sq_le hC hN hlog

theorem tendsto_exp_sq_atTop (C : ℝ) :
    Tendsto (fun N : ℕ ↦ Real.exp (C + (N : ℝ) ^ 2)) atTop atTop := by
  apply Real.tendsto_exp_atTop.comp
  exact tendsto_atTop_add_const_left atTop C
    ((tendsto_pow_atTop (show (2 : ℕ) ≠ 0 by norm_num)).comp tendsto_natCast_atTop_atTop)

/-- Endpoint little-o growth makes the secant slope at the packet
envelope little-o of `log N`. -/
theorem endpoint_secant_isLittleO_log (Φ : YoungFunction) (hΦ : GrowsSlowerThanEndpoint Φ)
    (C : ℝ) (hC : 0 ≤ C) :
    (fun N : ℕ ↦ Φ (Real.exp (C + (N : ℝ) ^ 2)) /
      Real.exp (C + (N : ℝ) ^ 2)) =o[atTop] (fun N : ℕ ↦ Real.log (N : ℝ)) := by
  let M : ℕ → ℝ := fun N ↦ Real.exp (C + (N : ℝ) ^ 2)
  have hc : (fun N ↦ Φ (M N)) =o[atTop] (fun N ↦ M N * paperLog 2 (M N)) :=
    hΦ.comp_tendsto (tendsto_exp_sq_atTop C)
  have hd := hc.mul_isBigO (isBigO_refl (fun N ↦ (M N)⁻¹) atTop)
  have hq : (fun N ↦ Φ (M N) / M N) =o[atTop] (fun N ↦ paperLog 2 (M N)) :=
    hd.congr (fun _ ↦ (div_eq_mul_inv _ _).symm) (fun N ↦ by
      have hne : M N ≠ 0 := Real.exp_ne_zero _
      field_simp)
  exact hq.trans_isBigO (paperLog_two_exp_sq_isBigO C hC)

theorem counterexampleModular_le_secant (Φ : YoungFunction) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ x, baseBump x ≤ C) {N : ℕ} (hN : 0 < N)
    (hlog : 1 ≤ Real.log (N : ℝ)) :
    counterexampleModular Φ N ≤
      (Φ (Real.exp (C + (N : ℝ) ^ 2)) / Real.exp (C + (N : ℝ) ^ 2)) *
        ((N : ℝ) / Real.log (N : ℝ)) := by
  have hlogpos : 0 < Real.log (N : ℝ) := by linarith
  have hc : Continuous (fun x ↦ packetSum N x / Real.log (N : ℝ)) :=
    (continuous_packetSum N).div_const _
  have hs : HasCompactSupport (fun x ↦ packetSum N x / Real.log (N : ℝ)) := by
    simp only [div_eq_mul_inv]
    exact (packetSum_hasCompactSupport N).mul_right
  have hn : ∀ x, 0 ≤ packetSum N x / Real.log (N : ℝ) :=
    fun x ↦ div_nonneg (packetSum_nonneg N x) hlogpos.le
  have hM : ∀ x, packetSum N x / Real.log (N : ℝ) ≤
      Real.exp (C + (N : ℝ) ^ 2) := fun x ↦
    (div_le_self (packetSum_nonneg N x) hlog).trans (packetSum_le_exp hC hbound hN x)
  rw [counterexampleModular_eq hN]
  calc
    (∫ x : ℝ, Φ (packetSum N x / Real.log (N : ℝ))) ≤
        (Φ (Real.exp (C + (N : ℝ) ^ 2)) / Real.exp (C + (N : ℝ) ^ 2)) *
          ∫ x : ℝ, packetSum N x / Real.log (N : ℝ) :=
      Φ.integral_le_secant hc hs hn (Real.exp_pos _) hM
    _ = _ := by rw [integral_div, packetSum_integral]

theorem counterexampleModular_nonneg (Φ : YoungFunction) {N : ℕ} (hN : 0 < N)
    (hlog : 0 ≤ Real.log (N : ℝ)) : 0 ≤ counterexampleModular Φ N := by
  rw [counterexampleModular_eq hN]
  exact integral_nonneg (fun x ↦ Φ.nonneg (div_nonneg (packetSum_nonneg N x) hlog))

/-- Equation `eq:modularcalc`: for every Young function growing strictly
slower than the endpoint, the modular of `N χ_N / log N` is `o(N)`. -/
theorem counterexampleModular_isLittleO (Φ : YoungFunction) (hΦ : GrowsSlowerThanEndpoint Φ) :
    counterexampleModular Φ =o[atTop] (fun N : ℕ ↦ (N : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := exists_baseBump_bound
  have hsec := endpoint_secant_isLittleO_log Φ hΦ C hC.le
  have hcast : Tendsto (fun N : ℕ ↦ (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  apply IsLittleO.of_bound
  intro ε hε
  filter_upwards [hsec.bound hε, hcast.eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp hcast).eventually_ge_atTop 1] with N hs hNr hlog
  change 1 ≤ Real.log (N : ℝ) at hlog
  have hN : 0 < N := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hNr)
  have hl : 0 < Real.log (N : ℝ) := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (counterexampleModular_nonneg Φ hN hl.le),
    Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg N)]
  rw [Real.norm_eq_abs, abs_of_nonneg
      (div_nonneg (Φ.nonneg (Real.exp_nonneg _)) (Real.exp_nonneg _)),
    Real.norm_eq_abs, abs_of_nonneg hl.le] at hs
  calc
    counterexampleModular Φ N ≤
        (Φ (Real.exp (C + (N : ℝ) ^ 2)) / Real.exp (C + (N : ℝ) ^ 2)) *
          ((N : ℝ) / Real.log (N : ℝ)) :=
      counterexampleModular_le_secant Φ hC hbound hN hlog
    _ ≤ (ε * Real.log (N : ℝ)) * ((N : ℝ) / Real.log (N : ℝ)) :=
      mul_le_mul_of_nonneg_right hs (div_nonneg (Nat.cast_nonneg N) hl.le)
    _ = ε * (N : ℝ) := by field_simp

theorem tendsto_counterexampleModular_div (Φ : YoungFunction)
    (hΦ : GrowsSlowerThanEndpoint Φ) :
    Tendsto (fun N : ℕ ↦ counterexampleModular Φ N / (N : ℝ)) atTop (𝓝 0) :=
  (counterexampleModular_isLittleO Φ hΦ).tendsto_div_nhds_zero

end QuadraticCarleson
