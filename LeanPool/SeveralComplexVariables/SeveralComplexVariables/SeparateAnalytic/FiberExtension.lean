/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.RemovableSingularity.Cauchy
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.SeparateAnalytic.HartogsLemma

/-!
# Hartogs' fiber extension lemma

A function of a base variable and one fiber variable, jointly analytic on a thin cylinder and
analytic on a larger disc in each fiber, is locally bounded on the larger cylinder. The fiber
Taylor coefficients are analytic in the base variable by Cauchy's formula on a small circle.
Cauchy's estimates on the large discs give a pointwise eventual bound on their roots, and
Hartogs' lemma makes this bound uniform near each base point, so the fiber Taylor series is
dominated by a geometric series near every point of the larger cylinder.

This is the continuation step in the proof of Hartogs' separate-analyticity theorem. Reference:
[Hörmander][Hormander1973] (1973), proof of Theorem 2.2.8; [Boas][Boas2013] (2013), Section 2.4.

## Main results

`fiberCoeff` is the Taylor coefficient of a fiber slice. `analyticOnNhd_fiberCoeff` is its
holomorphy in the base. `exists_eventually_norm_le_of_fiber_analytic` is local boundedness on
the larger cylinder. `exists_hartogs_fiber_radii` chooses the intermediate radii for the
geometric majorant.

## References

* [H. P. Boas, *Lecture Notes on Several Complex Variables*][Boas2013]
* [L. Hörmander, *An Introduction to Complex Analysis in Several Variables*][Hormander1973]
-/

public noncomputable section

open Complex Filter Function MeasureTheory Metric Set
open scoped Real Topology

namespace SeveralComplexVariables

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- Radii for the geometric majorant in Hartogs' fiber extension: an intermediate circle `σ < ρ` and
a contraction ratio `q < 1`. -/
theorem exists_hartogs_fiber_radii {b w₁ : ℂ} {R : ℝ} (hdist : dist w₁ b < R) :
    ∃ σ ρ ε q : ℝ, dist w₁ b < σ ∧ σ < ρ ∧ ρ < R ∧ 0 < σ ∧ 0 < ρ ∧ 0 < ε ∧
      0 < q ∧ q < 1 ∧ q = σ * (ρ⁻¹ + ε) := by
  obtain ⟨ρ, hρ₁, hρR⟩ := exists_between hdist
  have hρ : 0 < ρ := dist_nonneg.trans_lt hρ₁
  set σ : ℝ := (dist w₁ b + ρ) / 2
  have hσ₁ : dist w₁ b < σ := by dsimp [σ]; linarith
  have hσρ : σ < ρ := by dsimp [σ]; linarith
  have hσ0 : 0 < σ := by
    dsimp [σ]
    nlinarith [dist_nonneg (x := w₁) (y := b)]
  set ε : ℝ := (1 - σ / ρ) / (2 * σ)
  have hσρ' : σ / ρ < 1 := (div_lt_one hρ).mpr hσρ
  have hε0 : 0 < ε := div_pos (by linarith) (by positivity)
  set q : ℝ := σ * (ρ⁻¹ + ε)
  have hq_eq : q = (1 + σ / ρ) / 2 := by
    dsimp [q, ε]; field_simp; ring
  have hq1 : q < 1 := by rw [hq_eq]; linarith
  have hq0 : 0 < q := by rw [hq_eq]; positivity
  exact ⟨σ, ρ, ε, q, hσ₁, hσρ, hρR, hσ0, hρ, hε0, hq0, hq1, rfl⟩

omit [CompleteSpace F] in
/-- Cauchy's estimate for the scalar values of the Cauchy power series coefficients, from a bound on
the closed disc. -/
theorem norm_cauchyPowerSeries_apply_one_le {g : ℂ → F} {b : ℂ} {ρ M : ℝ} (hρ : 0 < ρ)
    (hM : ∀ w ∈ closedBall b ρ, ‖g w‖ ≤ M) (k : ℕ) :
    ‖cauchyPowerSeries g b ρ k (fun _ => 1)‖ ≤ M * ρ⁻¹ ^ k := by
  have hint : ∫ θ in (0:ℝ)..2 * π, ‖g (circleMap b ρ θ)‖ ≤ M * (2 * π) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * π)
      (f := fun θ => ‖g (circleMap b ρ θ)‖) (C := M) (fun θ _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        exact hM _ (circleMap_mem_closedBall b hρ.le θ))
    rw [sub_zero, abs_of_pos Real.two_pi_pos, Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  calc ‖cauchyPowerSeries g b ρ k (fun _ => 1)‖
      ≤ ‖cauchyPowerSeries g b ρ k‖ * ∏ _i : Fin k, ‖(1 : ℂ)‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖cauchyPowerSeries g b ρ k‖ := by simp
    _ ≤ ((2 * π)⁻¹ * ∫ θ in (0:ℝ)..2 * π, ‖g (circleMap b ρ θ)‖) * |ρ|⁻¹ ^ k :=
        norm_cauchyPowerSeries_le g b ρ k
    _ ≤ M * ρ⁻¹ ^ k := by
        rw [abs_of_pos hρ]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        calc (2 * π)⁻¹ * ∫ θ in (0:ℝ)..2 * π, ‖g (circleMap b ρ θ)‖
            ≤ (2 * π)⁻¹ * (M * (2 * π)) := by gcongr
          _ = M := by field_simp

/-- The Cauchy power series of a function analytic on a closed disc converges on the open disc, with
the radius given as an extended real number. -/
theorem hasFPowerSeriesOnBall_cauchyPowerSeries_of_analyticOnNhd {g : ℂ → F} {b : ℂ}
    {r : ℝ} (hr : 0 < r) (hg : AnalyticOnNhd ℂ g (closedBall b r)) :
    HasFPowerSeriesOnBall g (cauchyPowerSeries g b r) b (ENNReal.ofReal r) := by
  have := hg.differentiableOn.hasFPowerSeriesOnBall (R := ⟨r, hr.le⟩) hr
  rwa [ENNReal.ofReal_eq_coe_nnreal hr.le]

/-- Roots of a fixed positive constant tend to one. -/
theorem tendsto_rpow_inv_natCast_succ {M : ℝ} (hM : 0 < M) :
    Tendsto (fun n : ℕ => M ^ ((n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ => Real.log M * ((n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (Real.log M)).comp (tendsto_add_atTop_nat 1)
    simpa [Function.comp_def, div_eq_mul_inv] using this
  simpa [Function.comp_def, Real.rpow_def_of_pos hM] using
    Real.tendsto_exp_nhds_zero_nhds_one.comp h

/-- A root of an exponential-type bound is bounded by a root of the constant times the reciprocal
radius. -/
theorem rpow_inv_succ_le_of_le_mul_pow {x M ρ : ℝ} (hx : 0 ≤ x) (hM : 0 ≤ M) (hρ : 0 < ρ)
    (n : ℕ) (h : x ≤ M * ρ⁻¹ ^ (n + 1)) :
    x ^ ((n + 1 : ℕ) : ℝ)⁻¹ ≤ M ^ ((n + 1 : ℕ) : ℝ)⁻¹ * ρ⁻¹ := by
  calc x ^ ((n + 1 : ℕ) : ℝ)⁻¹ ≤ (M * ρ⁻¹ ^ (n + 1)) ^ ((n + 1 : ℕ) : ℝ)⁻¹ :=
        Real.rpow_le_rpow hx h (by positivity)
    _ = M ^ ((n + 1 : ℕ) : ℝ)⁻¹ * ρ⁻¹ := by
        rw [Real.mul_rpow hM (by positivity),
          Real.pow_rpow_inv_natCast (inv_nonneg.mpr hρ.le) n.succ_ne_zero]

/-- A sequence with a uniform exponential bound and an eventual geometric bound has a single
geometric majorant. -/
theorem le_geometric_of_bounds {a : ℕ → ℝ} {M s q : ℝ} {N : ℕ} (hM : 0 ≤ M) (hs : 0 ≤ s)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (h1 : ∀ k, a k ≤ M * s ^ k)
    (h2 : ∀ k, N + 1 ≤ k → a k ≤ q ^ k) (k : ℕ) :
    a k ≤ max 1 (M * max 1 s ^ N / q ^ N) * q ^ k := by
  have hqk : 0 ≤ q ^ k := pow_nonneg hq0.le k
  by_cases hk : N + 1 ≤ k
  · exact (h2 k hk).trans (le_mul_of_one_le_left hqk (le_max_left _ _))
  · have hkN : k ≤ N := by omega
    have hqN : q ^ N ≤ q ^ k := pow_le_pow_of_le_one hq0.le hq1 hkN
    have hC₀ : M * s ^ k ≤ M * max 1 s ^ N :=
      mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ hs (le_max_right 1 s) k).trans
        (pow_le_pow_right₀ (le_max_left 1 s) hkN)) hM
    have hqN0 : 0 < q ^ N := pow_pos hq0 N
    calc a k ≤ M * max 1 s ^ N := (h1 k).trans hC₀
      _ = M * max 1 s ^ N / q ^ N * q ^ N := by field_simp
      _ ≤ M * max 1 s ^ N / q ^ N * q ^ k :=
          mul_le_mul_of_nonneg_left hqN (div_nonneg (by positivity) hqN0.le)
      _ ≤ max 1 (M * max 1 s ^ N / q ^ N) * q ^ k :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hqk

/-- Fiber Taylor coefficients of a function of a base variable and a fiber variable, computed by
Cauchy's formula on the circle of radius `r` about `b` in the fiber. -/
private def fiberCoeff (f : E × ℂ → F) (b : ℂ) (r : ℝ) (k : ℕ) (z : E) : F :=
  cauchyPowerSeries (fun w => f (z, w)) b r k (fun _ => 1)

/-- The fiber coefficients are analytic in the base variable wherever the function is jointly
analytic on a cylinder containing the integration circle. -/
private theorem analyticOnNhd_fiberCoeff {D : Set E} (hD : IsOpen D) {b : ℂ} {r ε₁ : ℝ}
    (hr : 0 < r) (hrε : r < ε₁) {f : E × ℂ → F}
    (hf : AnalyticOnNhd ℂ f (D ×ˢ ball b ε₁)) (k : ℕ) :
    AnalyticOnNhd ℂ (fiberCoeff f b r k) D := by
  have hH : AnalyticOnNhd ℂ (fun q : E × ℂ => (1 / (q.2 - b)) ^ k • (q.2 - b)⁻¹ • f q)
      {q | q ∈ D ×ˢ ball b ε₁ ∧ q.2 ≠ b} := by
    intro q hq
    have hsub : AnalyticAt ℂ (fun q : E × ℂ => q.2 - b) q := analyticAt_snd.sub analyticAt_const
    have hne : q.2 - b ≠ 0 := sub_ne_zero.mpr hq.2
    exact ((analyticAt_const.div hsub hne).pow k).smul ((hsub.inv hne).smul (hf q hq.1))
  have h := analyticOnNhd_circleIntegral_kernel hD hH hr.le (c := b) (R := r) ?_
  · unfold fiberCoeff
    simp_rw [cauchyPowerSeries_apply]
    exact analyticOnNhd_const.smul h
  · intro z hz t ht
    have htb : dist t b = r := mem_sphere.mp ht
    refine ⟨⟨hz, ?_⟩, ?_⟩
    · rw [mem_ball, htb]; exact hrε
    · intro h
      have h' : t = b := h
      rw [h', dist_self] at htb
      exact hr.ne htb

omit [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace F] in
/-- A bound on a closed cylinder bounds all fiber coefficients over its base. -/
private theorem norm_fiberCoeff_le {f : E × ℂ → F} {b : ℂ} {r M : ℝ} (hr : 0 < r) {z : E}
    (hM : ∀ w ∈ closedBall b r, ‖f (z, w)‖ ≤ M) (k : ℕ) :
    ‖fiberCoeff f b r k z‖ ≤ M * r⁻¹ ^ k :=
  norm_cauchyPowerSeries_apply_one_le hr hM k

omit [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] in
/-- Fiber coefficients are independent of the radius when the fiber function is analytic on both
closed discs. -/
private theorem fiberCoeff_eq_of_radii {f : E × ℂ → F} {b : ℂ} {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    {z : E} (hgr : AnalyticOnNhd ℂ (fun w => f (z, w)) (closedBall b r))
    (hgρ : AnalyticOnNhd ℂ (fun w => f (z, w)) (closedBall b ρ)) (k : ℕ) :
    fiberCoeff f b r k z = cauchyPowerSeries (fun w => f (z, w)) b ρ k (fun _ => 1) := by
  unfold fiberCoeff
  rw [(hasFPowerSeriesOnBall_cauchyPowerSeries_of_analyticOnNhd hr
    hgr).hasFPowerSeriesAt.eq_formalMultilinearSeries
    (hasFPowerSeriesOnBall_cauchyPowerSeries_of_analyticOnNhd hρ hgρ).hasFPowerSeriesAt]

variable [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

/-- **Hartogs' fiber extension lemma.** A function jointly analytic on a thin cylinder over
an open base, whose fiber slices are analytic on a larger disc, is locally bounded on the
larger cylinder. The fiber Taylor series is dominated by a geometric series near each point,
by Hartogs' lemma applied to the roots of the fiber coefficients. -/
theorem exists_eventually_norm_le_of_fiber_analytic {D : Set E} (hD : IsOpen D) {b : ℂ}
    {ε₁ R : ℝ} (hε₁ : 0 < ε₁) {f : E × ℂ → F} (hf : AnalyticOnNhd ℂ f (D ×ˢ ball b ε₁))
    (hfib : ∀ z ∈ D, AnalyticOnNhd ℂ (fun w => f (z, w)) (ball b R))
    {z₁ : E} (hz₁ : z₁ ∈ D) {w₁ : ℂ} (hw₁ : w₁ ∈ ball b R) :
    ∃ M : ℝ, ∀ᶠ q in 𝓝 (z₁, w₁), ‖f q‖ ≤ M := by
  have hdist : dist w₁ b < R := mem_ball.mp hw₁
  obtain ⟨σ, ρ, ε, q, hσ₁, hσρ, hρR, hσ0, hρ, hε0, hq0, hq1, hq⟩ :=
    exists_hartogs_fiber_radii hdist
  obtain ⟨r₀, hr₀, hr₀D⟩ := nhds_basis_closedBall.mem_iff.mp (hD.mem_nhds hz₁)
  set r : ℝ := min r₀ (ε₁ / 2)
  have hr0 : 0 < r := lt_min hr₀ (by positivity)
  have hrε : r < ε₁ := (min_le_right _ _).trans_lt (by linarith)
  have hrD : closedBall z₁ r ⊆ D :=
    (closedBall_subset_closedBall (min_le_left _ _)).trans hr₀D
  have hcyl : closedBall z₁ r ×ˢ closedBall b r ⊆ D ×ˢ ball b ε₁ :=
    prod_mono hrD (closedBall_subset_ball hrε)
  obtain ⟨M₀, hM₀⟩ := ((isCompact_closedBall z₁ r).prod
    (isCompact_closedBall b r)).exists_bound_of_continuousOn (hf.continuousOn.mono hcyl)
  set M₁ : ℝ := max M₀ 1
  have hM₁1 : 1 ≤ M₁ := le_max_right _ _
  have hM₁0 : 0 < M₁ := by linarith
  have hM₁' : ∀ z ∈ closedBall z₁ r, ∀ w ∈ closedBall b r, ‖f (z, w)‖ ≤ M₁ :=
    fun z hz w hw => (hM₀ (z, w) ⟨hz, hw⟩).trans (le_max_left _ _)
  -- slice analyticity on the small and large closed discs
  have hgr : ∀ z ∈ D, AnalyticOnNhd ℂ (fun w => f (z, w)) (closedBall b r) := by
    intro z hz w hw
    exact (hf (z, w) ⟨hz, closedBall_subset_ball hrε hw⟩).comp_of_eq
      (analyticAt_const.prod analyticAt_id) rfl
  have hgρ : ∀ z ∈ D, AnalyticOnNhd ℂ (fun w => f (z, w)) (closedBall b ρ) :=
    fun z hz => (hfib z hz).mono (closedBall_subset_ball hρR)
  -- the coefficient family and its bounds
  have hp0 : ∀ n : ℕ, (0 : ℝ) < ((n + 1 : ℕ) : ℝ)⁻¹ := fun n => by positivity
  have hcan : ∀ n : ℕ, AnalyticOnNhd ℂ (fiberCoeff f b r (n + 1)) (closedBall z₁ r) :=
    fun n => (analyticOnNhd_fiberCoeff hD hr0 hrε hf (n + 1)).mono hrD
  have hB : ∀ n : ℕ, ∀ z ∈ closedBall z₁ r,
      ‖fiberCoeff f b r (n + 1) z‖ ^ ((n + 1 : ℕ) : ℝ)⁻¹ ≤ M₁ * r⁻¹ := by
    intro n z hz
    refine (rpow_inv_succ_le_of_le_mul_pow (norm_nonneg _) hM₁0.le hr0 n
      (norm_fiberCoeff_le hr0 (hM₁' z hz) (n + 1))).trans ?_
    gcongr
    exact Real.rpow_le_self_of_one_le hM₁1 (inv_le_one_of_one_le₀ (by exact_mod_cast n.succ_pos))
  have hlim : ∀ z ∈ closedBall z₁ r, ∀ δ > 0, ∀ᶠ n : ℕ in atTop,
      ‖fiberCoeff f b r (n + 1) z‖ ^ ((n + 1 : ℕ) : ℝ)⁻¹ ≤ ρ⁻¹ + δ := by
    intro z hz δ hδ
    have hzD : z ∈ D := hrD hz
    obtain ⟨M₂, hM₂⟩ := (isCompact_closedBall b ρ).exists_bound_of_continuousOn
      (hgρ z hzD).continuousOn
    have hM₃0 : 0 < max M₂ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hcoef : ∀ n : ℕ, ‖fiberCoeff f b r (n + 1) z‖ ^ ((n + 1 : ℕ) : ℝ)⁻¹ ≤
        (max M₂ 1) ^ ((n + 1 : ℕ) : ℝ)⁻¹ * ρ⁻¹ := by
      intro n
      apply rpow_inv_succ_le_of_le_mul_pow (norm_nonneg _) hM₃0.le hρ
      rw [fiberCoeff_eq_of_radii hr0 hρ (hgr z hzD) (hgρ z hzD)]
      exact norm_cauchyPowerSeries_apply_one_le hρ
        (fun w hw => (hM₂ w hw).trans (le_max_left _ _)) _
    have ht := ((tendsto_rpow_inv_natCast_succ hM₃0).mul_const ρ⁻¹).eventually
      (eventually_le_nhds (show 1 * ρ⁻¹ < ρ⁻¹ + δ by linarith))
    filter_upwards [ht] with n hn using (hcoef n).trans hn
  obtain ⟨r', hr'0, hev⟩ := eventually_norm_rpow_lt_on_ball hr0 hp0 hcan hB hlim hε0
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  have hbig : ∀ k, N + 1 ≤ k → ∀ z ∈ ball z₁ r',
      ‖fiberCoeff f b r k z‖ ≤ (ρ⁻¹ + ε) ^ k := by
    intro k hk z hz
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    have := hN n (by omega) z hz
    rw [Real.rpow_inv_lt_iff_of_pos (norm_nonneg _) (by positivity) (by positivity),
      Real.rpow_natCast] at this
    exact this.le
  -- the geometric majorant
  refine ⟨max 1 (M₁ * max 1 (σ / r) ^ N / q ^ N) * (1 - q)⁻¹, ?_⟩
  have hopen : IsOpen (ball z₁ (min r' r) ×ˢ ball b σ) := isOpen_ball.prod isOpen_ball
  have hmem : (z₁, w₁) ∈ ball z₁ (min r' r) ×ˢ ball b σ :=
    ⟨mem_ball_self (lt_min hr'0 hr0), mem_ball.mpr hσ₁⟩
  filter_upwards [hopen.mem_nhds hmem]
  rintro ⟨z, w⟩ ⟨hz, hw⟩
  have hzr' : z ∈ ball z₁ r' := ball_subset_ball (min_le_left _ _) hz
  have hzr : z ∈ closedBall z₁ r := ball_subset_closedBall (ball_subset_ball (min_le_right _ _) hz)
  have hzD : z ∈ D := hrD hzr
  have hwσ : ‖w - b‖ < σ := by rwa [← dist_eq_norm]
  have hps := hasFPowerSeriesOnBall_cauchyPowerSeries_of_analyticOnNhd hρ (hgρ z hzD)
  have hsum := hps.hasSum (y := w - b) (by
    change edist (w - b) 0 < ENNReal.ofReal ρ
    rw [edist_lt_ofReal, dist_zero_right]
    exact hwσ.trans hσρ)
  rw [add_sub_cancel] at hsum
  have hterm (k : ℕ) : (cauchyPowerSeries (fun w => f (z, w)) b ρ k fun _ => w - b) =
      (w - b) ^ k • fiberCoeff f b r k z := by
    rw [fiberCoeff_eq_of_radii hr0 hρ (hgr z hzD) (hgρ z hzD)]
    simp
  refine hsum.norm_le_of_bounded ((hasSum_geometric_of_lt_one hq0.le hq1).mul_left _) ?_
  apply le_geometric_of_bounds (s := σ / r) hM₁0.le (by positivity) hq0 hq1.le
  · intro k
    rw [hterm, norm_smul, norm_pow]
    calc ‖w - b‖ ^ k * ‖fiberCoeff f b r k z‖ ≤ σ ^ k * (M₁ * r⁻¹ ^ k) :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hwσ.le k)
            (norm_fiberCoeff_le hr0 (hM₁' z hzr) k) (norm_nonneg _) (by positivity)
      _ = M₁ * (σ / r) ^ k := by rw [div_pow, inv_pow]; ring
  · intro k hk
    rw [hterm, norm_smul, norm_pow, hq, mul_pow]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hwσ.le k) (hbig k hk z hzr')
      (norm_nonneg _) (by positivity)

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
