/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.GeneralizedResidueTheory.Residue.FlatnessTransfer.PerTermVanishing

/-!
# Per-Term PV Vanishing: CPV Helpers and Assembly

CPV helpers for continuous functions, holomorphic CPV vanishing on convex domains,
scalar/sum lemmas for CPV integrands, integrability, and the assembly of
per-term vanishing into the complete higher-order cancellation.

## Main Results

* `tendsto_cpv_of_continuousOn_zero_integral` — CPV with zero contour integral
* `holomorphic_cpv_tendsto_zero_on_convex` — holomorphic CPV → 0
* `cpvIntegrandOn_const_smul` / `cpvIntegrandOn_add` / `cpvIntegrandOn_finset_sum`
* `intervalIntegrable_cpvIntegrandOn_of_continuousOn_diff`
* `residueAt_sub_residueSum_eq_zero` — residue of f minus residue sum vanishes
* `cpv_tendsto_zero_of_add_decomposition` — final assembly
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

namespace GeneralizedResidueTheory

/-! ### Helper: CPV of a function continuous along γ with zero contour integral

If g is continuous on γ's image and ∮_γ g dz = 0, then cpv(S0, g, ε) → 0.
The CPV integrand converges a.e. to g(γ(t)) * γ'(t) as ε → 0 (the crossing
set has measure zero), and is dominated by ‖g(γ(t))‖ * ‖γ'(t)‖. By DCT, the
limit equals ∮_γ g dz = 0. -/

/-- CPV integral of a function continuous along γ with zero ordinary contour
integral tends to 0. This is the DCT core of the assembly proof, abstracting
the zero-integral condition. -/
theorem tendsto_cpv_of_continuousOn_zero_integral
    (S0 : Finset ℂ) (g : ℂ → ℂ) (γ : PiecewiseC1Immersion)
    (hg_cont : ContinuousOn g (γ.toFun '' Icc γ.a γ.b))
    (h_integral_zero : ∫ t in γ.a..γ.b, g (γ.toFun t) * deriv γ.toFun t = 0) :
    Tendsto (fun ε => ∫ t in γ.a..γ.b,
      cauchyPrincipalValueIntegrandOn S0 g γ.toFun ε t) (𝓝[>] 0) (𝓝 0) := by
  have hgγ_cont : ContinuousOn (fun t => g (γ.toFun t)) (Set.uIcc γ.a γ.b) :=
    Set.uIcc_of_le (le_of_lt γ.hab) ▸ hg_cont.comp
      γ.toPiecewiseC1Curve.continuous_toFun (fun t ht => Set.mem_image_of_mem _ ht)
  have h_ord_int : IntervalIntegrable (fun t => g (γ.toFun t) * deriv γ.toFun t)
      MeasureTheory.volume γ.a γ.b :=
    (piecewiseC1_deriv_intervalIntegrable γ.toPiecewiseC1Curve
      (piecewiseC1Immersion_deriv_bounded γ)).continuousOn_mul hgγ_cont
  rw [← h_integral_zero]
  have h_ae_not_in_S0 := ae_forall_ne_of_finite_crossings S0 γ
  exact intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun t => ‖g (γ.toFun t) * deriv γ.toFun t‖)
    (by filter_upwards [self_mem_nhdsWithin] with ε (hε : (0 : ℝ) < ε)
        have h_int := intervalIntegrable_cauchyPrincipalValueIntegrandOn (S0 := S0) hε hg_cont
        rw [intervalIntegrable_iff] at h_int
        exact h_int.aestronglyMeasurable)
    (by filter_upwards [self_mem_nhdsWithin] with ε (_hε : (0 : ℝ) < ε)
        apply ae_of_all; intro t ht
        simp only [cauchyPrincipalValueIntegrandOn]
        split_ifs
        · simp only [norm_zero]; exact norm_nonneg _
        · exact le_refl _)
    h_ord_int.norm
    (by filter_upwards [h_ae_not_in_S0] with t h_not_in ht_in
        simp only [cauchyPrincipalValueIntegrandOn]
        have h_not_in' := h_not_in ht_in
        by_cases hS0_empty : S0 = ∅
        · have : ∀ ε, ¬∃ s ∈ S0, ‖γ.toFun t - s‖ ≤ ε := by
            intro ε h_ex; obtain ⟨s, hs, _⟩ := h_ex
            exact absurd hs (hS0_empty ▸ Finset.notMem_empty s)
          apply tendsto_const_nhds.congr'
          filter_upwards with ε; rw [if_neg (this ε)]
        · have hS0_ne : S0.Nonempty := Finset.nonempty_of_ne_empty hS0_empty
          let δ := S0.inf' hS0_ne (fun s => ‖γ.toFun t - s‖)
          have hδ_pos : 0 < δ :=
            (Finset.lt_inf'_iff hS0_ne).mpr (fun s hs =>
              norm_pos_iff.mpr (sub_ne_zero.mpr (h_not_in' s hs)))
          apply tendsto_const_nhds.congr'
          filter_upwards [Ioo_mem_nhdsGT hδ_pos] with ε hε
          have h_no_near : ¬∃ s ∈ S0, ‖γ.toFun t - s‖ ≤ ε := by
            push Not; intro s hs
            exact lt_of_lt_of_le hε.2 (Finset.inf'_le _ hs)
          rw [if_neg h_no_near])

/-! ### Sublemma 3: Holomorphic CPV integral → 0 on closed curve -/

/-- **Sublemma 3**: For a function holomorphic on a convex open `U` containing the
closed curve `γ`, the multi-point CPV integral tends to 0.

The CPV integrand `1_{∀s∈S0, ‖γ(t)-s‖>ε} · g(γ(t)) · γ'(t)` converges a.e.
to `g(γ(t)) · γ'(t)` as `ε → 0` (the cutout set shrinks to a null set), and
is dominated by `‖g(γ(t))‖ · ‖γ'(t)‖` (bounded since `g` is continuous on
the compact image of `γ`). By DCT, the CPV integral converges to the ordinary
integral `∮_γ g dz`, which is 0 by Cauchy's integral theorem on convex `U`. -/
theorem holomorphic_cpv_tendsto_zero_on_convex (U : Set ℂ) (hU : IsOpen U)
    (hU_convex : Convex ℝ U) (S0 : Finset ℂ) (g : ℂ → ℂ)
    (hg : DifferentiableOn ℂ g U) (γ : PiecewiseC1Immersion)
    (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U) :
    Tendsto (fun ε =>
      ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0 g γ.toFun ε t)
    (𝓝[>] 0) (𝓝 0) := by
  have hγ_cont := γ.toPiecewiseC1Curve.continuous_toFun
  have hg_cont_U : ContinuousOn g U := hg.continuousOn
  have hg_cont_image : ContinuousOn g (γ.toFun '' Icc γ.a γ.b) :=
    hg_cont_U.mono (Set.image_subset_iff.mpr (fun t ht => hγ_in_U t ht))
  have hgγ_cont : ContinuousOn (fun t => g (γ.toFun t)) (Set.uIcc γ.a γ.b) := by
    rw [Set.uIcc_of_le (le_of_lt γ.hab)]
    exact hg_cont_U.comp hγ_cont (fun t ht => hγ_in_U t ht)
  have h_ord_int : IntervalIntegrable (fun t => g (γ.toFun t) * deriv γ.toFun t)
      MeasureTheory.volume γ.a γ.b :=
    (piecewiseC1_deriv_intervalIntegrable γ.toPiecewiseC1Curve
      (piecewiseC1Immersion_deriv_bounded γ)).continuousOn_mul hgγ_cont
  obtain ⟨F, hF⟩ := holomorphic_convex_primitive hU_convex hU
    ⟨γ.toFun γ.a, hγ_in_U γ.a (left_mem_Icc.mpr (le_of_lt γ.hab))⟩ hg
  have h_Fγ_cont : ContinuousOn (F ∘ γ.toFun) (Icc γ.a γ.b) := by
    intro t ht
    exact ((hF (γ.toFun t) (hγ_in_U t ht)).continuousAt).continuousWithinAt.comp
      (hγ_cont t ht) (mapsTo_image γ.toFun _)
  have h_deriv' : ∀ t ∈ Ioo γ.a γ.b \ (↑γ.partition ∩ Ioo γ.a γ.b),
      HasDerivAt (F ∘ γ.toFun) (g (γ.toFun t) * deriv γ.toFun t) t := fun t ⟨ht, hp⟩ =>
    (hF (γ.toFun t) (hγ_in_U t (Ioo_subset_Icc_self ht))).comp_of_eq t
      ((γ.smooth_off_partition t (Ioo_subset_Icc_self ht)
        (fun h => hp ⟨h, ht⟩)).hasDerivAt) rfl
  have h_ord_zero : ∫ t in γ.a..γ.b, g (γ.toFun t) * deriv γ.toFun t = 0 := by
    rw [MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le (F ∘ γ.toFun)
        (fun t => g (γ.toFun t) * deriv γ.toFun t) (le_of_lt γ.hab)
        (γ.partition.finite_toSet.inter_of_left _).countable h_Fγ_cont h_deriv' h_ord_int,
      Function.comp_apply, Function.comp_apply,
      (hγ_closed : γ.toFun γ.a = γ.toFun γ.b), sub_self]
  exact tendsto_cpv_of_continuousOn_zero_integral S0 g γ hg_cont_image h_ord_zero

/-! ### Helper: CPV integral of scalar multiple -/

/-- CPV integrand of `c • f` equals `c • cpv(f)` pointwise (the indicator set is the same). -/
lemma cpvIntegrandOn_const_smul (S0 : Finset ℂ) (c : ℂ) (f : ℂ → ℂ)
    (γ : ℝ → ℂ) (ε : ℝ) (t : ℝ) :
    cauchyPrincipalValueIntegrandOn S0 (fun z => c * f z) γ ε t =
    c * cauchyPrincipalValueIntegrandOn S0 f γ ε t := by
  simp only [cauchyPrincipalValueIntegrandOn]
  split_ifs <;> ring

/-- CPV integrand of `f + g` equals `cpv(f) + cpv(g)` pointwise (same indicator). -/
lemma cpvIntegrandOn_add (S0 : Finset ℂ) (f g : ℂ → ℂ)
    (γ : ℝ → ℂ) (ε : ℝ) (t : ℝ) :
    cauchyPrincipalValueIntegrandOn S0 (fun z => f z + g z) γ ε t =
    cauchyPrincipalValueIntegrandOn S0 f γ ε t +
    cauchyPrincipalValueIntegrandOn S0 g γ ε t := by
  simp only [cauchyPrincipalValueIntegrandOn]
  split_ifs <;> ring

/-- CPV integrand of a finset sum decomposes. -/
lemma cpvIntegrandOn_finset_sum {ι : Type*} (S0 : Finset ℂ) (T : Finset ι)
    (f : ι → ℂ → ℂ) (γ : ℝ → ℂ) (ε : ℝ) (t : ℝ) :
    cauchyPrincipalValueIntegrandOn S0 (fun z => ∑ i ∈ T, f i z) γ ε t =
    ∑ i ∈ T, cauchyPrincipalValueIntegrandOn S0 (f i) γ ε t := by
  simp only [cauchyPrincipalValueIntegrandOn]
  split_ifs <;> simp only [Finset.sum_const_zero, Finset.sum_mul]

/-- Integrability of CPV integrand for functions continuous on U \ S0.
For any g continuous on U \ S0 with γ mapping into U, the multi-point CPV
integrand is interval integrable on [a,b] for fixed ε > 0. The key insight
is that the CPV integrand is bounded (it's either 0 or g(γ(t)) * γ'(t) where
γ(t) is far from all poles) and ae strongly measurable (continuous off a finite
set within [a,b]). -/
lemma intervalIntegrable_cpvIntegrandOn_of_continuousOn_diff
    (U : Set ℂ) (S0 : Finset ℂ) (g : ℂ → ℂ)
    (hg_cont : ContinuousOn g (U \ ↑S0)) (γ : PiecewiseC1Immersion)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U) (ε : ℝ) (hε : 0 < ε) :
    IntervalIntegrable
      (cauchyPrincipalValueIntegrandOn S0 g γ.toFun ε) volume γ.a γ.b := by
  have hγ_cont := γ.toPiecewiseC1Curve.continuous_toFun
  obtain ⟨Mγ', hMγ'⟩ := piecewiseC1Immersion_deriv_bounded γ
  have h_safe_closed : IsClosed ({z : ℂ | ∀ s ∈ S0, ε ≤ ‖z - s‖}) := by
    have : {z : ℂ | ∀ s ∈ S0, ε ≤ ‖z - s‖} =
        ⋂ s ∈ (↑S0 : Set ℂ), {z | ε ≤ ‖z - s‖} := by ext z; simp [Set.mem_iInter]
    rw [this]; exact isClosed_biInter fun s _ =>
      isClosed_le continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))
  have h_safe_compact : IsCompact
      ((γ.toFun '' Icc γ.a γ.b) ∩ {z | ∀ s ∈ S0, ε ≤ ‖z - s‖}) :=
    (isCompact_Icc.image_of_continuousOn hγ_cont).inter_right h_safe_closed
  have h_safe_sub :
      (γ.toFun '' Icc γ.a γ.b) ∩
        {z | ∀ s ∈ S0, ε ≤ ‖z - s‖} ⊆ U \ ↑S0 := by
    intro z hz
    obtain ⟨⟨t, ht, rfl⟩, hz_safe⟩ := hz
    exact ⟨hγ_in_U t ht, fun hzS0 => by
      have h1 := hz_safe (γ.toFun t) (Finset.mem_coe.mp hzS0)
      simp only [sub_self, norm_zero] at h1; linarith⟩
  obtain ⟨Mg, hMg⟩ := h_safe_compact.exists_bound_of_continuousOn (hg_cont.mono h_safe_sub)
  have h_bound : ∀ t ∈ Icc γ.a γ.b,
      ‖cauchyPrincipalValueIntegrandOn S0 g γ.toFun ε t‖ ≤ |Mg| * |Mγ'| + 1 := by
    intro t ht
    simp only [cauchyPrincipalValueIntegrandOn]
    split_ifs with h
    · simp only [norm_zero]; positivity
    · push Not at h
      calc ‖g (γ.toFun t) * deriv γ.toFun t‖
          = ‖g (γ.toFun t)‖ * ‖deriv γ.toFun t‖ := norm_mul _ _
        _ ≤ |Mg| * |Mγ'| := by
            apply mul_le_mul
            · exact (hMg _
                ⟨⟨t, ht, rfl⟩,
                  fun s hs => le_of_lt (h s hs)⟩).trans
                (le_abs_self _)
            · exact (hMγ' t ht).trans (le_abs_self _)
            · exact norm_nonneg _
            · positivity
        _ ≤ |Mg| * |Mγ'| + 1 := le_add_of_nonneg_right one_pos.le
  set cpv_fn := cauchyPrincipalValueIntegrandOn S0 g γ.toFun ε
  have h_cpv_aesm : AEStronglyMeasurable cpv_fn (volume.restrict (Icc γ.a γ.b)) := by
    let GoodSet := {t : ℝ | ∀ s' ∈ S0, ε < ‖γ.toFun t - s'‖}
    have hGoodSet_meas : MeasurableSet (GoodSet ∩ Icc γ.a γ.b) :=
      measurableSet_goodSet_Icc S0 γ ε
    have hgγ_cont_good : ContinuousOn (fun t => g (γ.toFun t))
        (GoodSet ∩ Icc γ.a γ.b) := by
      apply ContinuousOn.comp (hg_cont.mono h_safe_sub) (hγ_cont.mono inter_subset_right)
      intro t ⟨ht_good, ht_Icc⟩
      exact ⟨mem_image_of_mem _ ht_Icc, fun s' hs' => le_of_lt (ht_good s' hs')⟩
    have h_prod_meas : AEStronglyMeasurable (fun t => g (γ.toFun t) * deriv γ.toFun t)
        (volume.restrict (GoodSet ∩ Icc γ.a γ.b)) :=
      (hgγ_cont_good.aestronglyMeasurable hGoodSet_meas).mul
        ((aesm_deriv_on_Icc γ).mono_measure (Measure.restrict_mono Set.inter_subset_right le_rfl))
    have h_pw := AEStronglyMeasurable.piecewise hGoodSet_meas h_prod_meas
      (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : ℝ => (0 : ℂ))
        (volume.restrict (GoodSet ∩ Icc γ.a γ.b)ᶜ))
    have h_ae_eq : cpv_fn =ᵐ[volume.restrict (Icc γ.a γ.b)]
        (GoodSet ∩ Icc γ.a γ.b).piecewise
          (fun t => g (γ.toFun t) * deriv γ.toFun t) (fun _ => (0 : ℂ)) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      change cauchyPrincipalValueIntegrandOn S0 g γ.toFun ε t = _
      simp only [cauchyPrincipalValueIntegrandOn]
      by_cases ht_good : t ∈ GoodSet ∩ Icc γ.a γ.b
      · rw [Set.piecewise_eq_of_mem _ _ _ ht_good, if_neg]
        push Not; exact ht_good.1
      · rw [Set.piecewise_eq_of_notMem _ _ _ ht_good, if_pos]
        exact by_contra (fun h => by push Not at h; exact ht_good ⟨h, ht⟩)
    exact (h_pw.mono_measure Measure.restrict_le_self).congr h_ae_eq.symm
  have h_int : IntegrableOn cpv_fn (Icc γ.a γ.b) volume :=
    IntegrableOn.of_bound
      (show volume (Icc γ.a γ.b) < ⊤ by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
      h_cpv_aesm (|Mg| * |Mγ'| + 1)
      (by filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht; exact h_bound t ht)
  exact (Set.uIcc_of_le (le_of_lt γ.hab) ▸ h_int).intervalIntegrable

/-! ### Assembly helper: CPV of h = f - f_res tends to 0

This helper packages the assembly of Sublemmas 1-3 into the main bridge lemma.
It shows that `∫ cpv(S0, h, ε) → 0` where `h z = f z - Σ res(f,s)/(z-s)`.

The proof decomposes h into:
- **Polar terms** at each crossed point: `a_k/(z-s)^{k+1}` for `k ≥ 1`,
  each tending to 0 by `multipoint_pv_zpow_tendsto_zero` (Sublemma 2).
- **Holomorphic remainder**: continuous along γ with zero contour integral,
  tending to 0 by `tendsto_cpv_of_continuousOn_zero_integral`.

The identification `a_0 = residueAt f s` uses `residueAt_eq_laurent_head_coeff`
(Sublemma 1). -/

/-- Circle integrals of a meromorphic `f` are constant for small radii: if `f` is
analytic on `ball s rf \ {s}`, then `∮_{C(s,r)} f = ∮_{C(s,R₀)} f` for `r ≤ R₀ < rf`.
The proof multiplies by `(z-s)` to get a holomorphic `F` on the annulus, applies
the annulus integral identity, then divides back by `(z-s)⁻¹`. -/
private lemma circleIntegral_const_of_meromorphicAt_aux (f : ℂ → ℂ) (s : ℂ) (rf R₀ : ℝ)
    (hR₀_pos : 0 < R₀) (hR₀_lt_rf : R₀ < rf)
    (hf_analytic_at : ∀ z, z ∈ Metric.ball s rf → z ≠ s → AnalyticAt ℂ f z)
    (r : ℝ) (hr_pos : 0 < r) (hr_le : r ≤ R₀) :
    (∮ z in C(s, r), f z) = (∮ z in C(s, R₀), f z) := by
  have hR₀_ne : R₀ ≠ 0 := ne_of_gt hR₀_pos
  have h_inv_smul : ∀ ρ (hρ_ne : ρ ≠ 0),
      Set.EqOn (fun z => (z - s)⁻¹ • ((z - s) * f z)) f (Metric.sphere s ρ) := by
    intro ρ hρ_ne z hz
    have h_ne : z ≠ s := by
      intro heq; rw [heq, Metric.mem_sphere, dist_self] at hz
      exact hρ_ne hz.symm
    simp only [smul_eq_mul, inv_mul_cancel_left₀ (sub_ne_zero.mpr h_ne)]
  set F : ℂ → ℂ := fun z => (z - s) * f z with hF_def
  have hF_analytic : ∀ z, z ∈ Metric.ball s rf → z ≠ s → AnalyticAt ℂ F z := by
    intro z hz hne
    exact (analyticAt_id.sub analyticAt_const).mul (hf_analytic_at z hz hne)
  have hF_cont : ContinuousOn F (Metric.closedBall s R₀ \ Metric.ball s r) := by
    intro z ⟨hz_cb, hz_not_ball⟩
    have h_ne : z ≠ s := by
      intro heq; rw [heq, Metric.mem_ball, dist_self, not_lt] at hz_not_ball; linarith
    exact (hF_analytic z (Metric.mem_ball.mpr (lt_of_le_of_lt
      (Metric.mem_closedBall.mp hz_cb) hR₀_lt_rf)) h_ne).continuousAt.continuousWithinAt
  have hF_diff : ∀ z ∈ (Metric.ball s R₀ \ Metric.closedBall s r) \ (∅ : Set ℂ),
      DifferentiableAt ℂ F z := by
    intro z ⟨⟨hz_ball, hz_not_cb⟩, _⟩
    have h_ne : z ≠ s := by
      intro heq; subst heq
      exact hz_not_cb (Metric.mem_closedBall_self hr_pos.le)
    exact (hF_analytic z (Metric.mem_ball.mpr
      (lt_trans (Metric.mem_ball.mp hz_ball) hR₀_lt_rf)) h_ne).differentiableAt
  have h_annulus :=
    Complex.circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable
      hr_pos hr_le Set.countable_empty hF_cont hF_diff
  rw [circleIntegral.integral_congr hr_pos.le (h_inv_smul r (ne_of_gt hr_pos)),
    circleIntegral.integral_congr hR₀_pos.le (h_inv_smul R₀ hR₀_ne)] at h_annulus
  exact h_annulus.symm

/-- Circle integral of `∑ s' ∈ S0, c(s') / (z - s')` around `s ∈ S0` at radius
`r < dist(s, S0 \ {s})` equals `c(s) * 2πi`. The poles `s' ≠ s` are outside
the circle (by the separation hypothesis), so their contributions vanish. -/
private lemma circleIntegral_simple_pole_sum
    (S0 : Finset ℂ) (c : ℂ → ℂ) (s : ℂ) (hs : s ∈ S0) (r : ℝ) (hr_pos : 0 < r)
    (h_no_pole : ∀ p ∈ S0, ∀ z ∈ Metric.sphere s r, z - p ≠ 0)
    (h_no_pole_cb : ∀ p ∈ S0.erase s, ∀ z ∈ Metric.closedBall s r, z - p ≠ 0) :
    (∮ z in C(s, r), ∑ s' ∈ S0, c s' / (z - s')) =
      c s * (2 * ↑Real.pi * I) := by
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  have hs_not : s ∉ Metric.sphere s r := by simp [hr_ne.symm]
  rw [show (fun z => ∑ s' ∈ S0, c s' / (z - s')) =
      (fun z => c s / (z - s) +
        ∑ s' ∈ S0.erase s, c s' / (z - s'))
    from funext (fun z => (Finset.add_sum_erase S0
      (fun s' => c s' / (z - s')) hs).symm)]
  have hci_s : CircleIntegrable (fun z => c s / (z - s)) s r :=
    (ContinuousOn.div continuousOn_const (continuousOn_id.sub continuousOn_const)
      (fun z hz => sub_ne_zero.mpr (ne_of_mem_of_not_mem hz hs_not))).circleIntegrable hr_pos.le
  have hci_rest : CircleIntegrable
      (fun z => ∑ s' ∈ S0.erase s, c s' / (z - s')) s r := by
    apply ContinuousOn.circleIntegrable hr_pos.le
    apply continuousOn_finsetSum; intro p hp
    exact ContinuousOn.div continuousOn_const (continuousOn_id.sub continuousOn_const)
      (fun z hz => h_no_pole p (Finset.mem_of_mem_erase hp) z hz)
  rw [circleIntegral.integral_add hci_s hci_rest,
    show (fun z => c s / (z - s)) = (fun z => c s * (z - s)⁻¹)
      from funext (fun z => div_eq_mul_inv _ _),
    circleIntegral.integral_const_mul, circleIntegral.integral_sub_center_inv s hr_ne]
  suffices h_rest : (∮ z in C(s, r), ∑ s' ∈ S0.erase s, c s' / (z - s')) = 0 by
    rw [h_rest, add_zero]
  have h_rest_cont : ContinuousOn
      (fun z => ∑ s' ∈ S0.erase s, c s' / (z - s')) (Metric.closedBall s r) := by
    apply continuousOn_finsetSum; intro p hp
    exact ContinuousOn.div continuousOn_const (continuousOn_id.sub continuousOn_const)
      (fun z hz => h_no_pole_cb p hp z hz)
  have h_rest_diff : ∀ z ∈ (Metric.ball s r) \ (∅ : Set ℂ), DifferentiableAt ℂ
      (fun z => ∑ s' ∈ S0.erase s, c s' / (z - s')) z := by
    intro z ⟨hz, _⟩
    apply DifferentiableAt.fun_sum; intro p hp
    exact (differentiableAt_const (c p)).div
      (differentiableAt_id.sub (differentiableAt_const p))
      (h_no_pole_cb p hp z (Metric.ball_subset_closedBall hz))
  exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr_pos.le
    Set.countable_empty h_rest_cont h_rest_diff

/-- Helper: `residueAt (f - Σ res(f,s')/(z-s')) s = 0` for `s ∈ S0`.
The function `h z = f z - Σ_{s' ∈ S0} residueAt f s' / (z - s')` has the same
higher-order poles as `f` at `s` but no simple pole (the `s' = s` term in the
sum cancels the residue). Hence `residueAt h s = 0`.

The proof uses circle integral decomposition: for small `r`,
`∮_{C(s,r)} h = ∮ f - Σ residueAt f s' * ∮ 1/(z-s')`. For `s' ≠ s` with
`|s'-s| > r`, `∮ 1/(z-s') = 0` (Cauchy); for `s' = s`, `∮ 1/(z-s) = 2πi`.
So `(2πi)⁻¹ ∮ h = (2πi)⁻¹ ∮ f - residueAt f s`. Taking `r → 0`:
`residueAt h s = residueAt f s - residueAt f s = 0`. -/
lemma residueAt_sub_residueSum_eq_zero
    (S0 : Finset ℂ) (f : ℂ → ℂ) (s : ℂ) (hs : s ∈ S0)
    (hMero : MeromorphicAt f s) :
    residueAt (fun z => f z - ∑ s' ∈ S0, residueAt f s' / (z - s')) s = 0 := by
  change limUnder (𝓝[>] (0 : ℝ)) (fun r =>
    (2 * ↑Real.pi * I)⁻¹ * ∮ z in C(s, r),
      f z - ∑ s' ∈ S0, residueAt f s' / (z - s')) = 0
  apply Filter.Tendsto.limUnder_eq
  have h_min_dist : ∃ δ > 0, ∀ s' ∈ S0, s' ≠ s → δ ≤ dist s' s := by
    by_cases h_other : ∃ s' ∈ S0, s' ≠ s
    · obtain ⟨s', hs', hne⟩ := h_other
      have h_nonempty : (S0.filter (· ≠ s)).Nonempty :=
        ⟨s', Finset.mem_filter.mpr ⟨hs', hne⟩⟩
      exact ⟨(S0.filter (· ≠ s)).inf' h_nonempty (fun s' => dist s' s),
        (Finset.lt_inf'_iff h_nonempty).mpr (fun b hb => dist_pos.mpr (Finset.mem_filter.mp hb).2),
        fun s' hs' hne' => Finset.inf'_le _ (Finset.mem_filter.mpr ⟨hs', hne'⟩)⟩
    · push Not at h_other
      exact ⟨1, one_pos, fun s' hs' hne' => absurd (h_other s' hs') hne'⟩
  obtain ⟨δ, hδ_pos, hδ_sep⟩ := h_min_dist
  have hf_ev_analytic := hMero.eventually_analyticAt
  rw [Filter.Eventually, Metric.mem_nhdsWithin_iff] at hf_ev_analytic
  obtain ⟨rf, hrf_pos, hrf_analytic⟩ := hf_ev_analytic
  set ρ := min δ rf with hρ_def
  have hρ_pos : 0 < ρ := lt_min hδ_pos hrf_pos
  have h2piI_ne : (2 : ℂ) * ↑Real.pi * I ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  set R₀ := ρ / 2 with hR₀_def
  have hR₀_pos : 0 < R₀ := by positivity
  have hR₀_lt_ρ : R₀ < ρ := by linarith
  have hR₀_lt_δ : R₀ < δ := lt_of_lt_of_le hR₀_lt_ρ (min_le_left _ _)
  have hR₀_lt_rf : R₀ < rf := lt_of_lt_of_le hR₀_lt_ρ (min_le_right _ _)
  have hR₀_ne : R₀ ≠ 0 := ne_of_gt hR₀_pos
  have hf_analytic_at : ∀ z, z ∈ Metric.ball s rf → z ≠ s → AnalyticAt ℂ f z := by
    intro z hz hne
    exact hrf_analytic ⟨hz, Set.mem_compl_singleton_iff.mpr hne⟩
  have hf_cont_sphere : ∀ r, 0 < r → r < rf → ContinuousOn f (Metric.sphere s r) := by
    intro r hr_pos hr_lt z hz
    exact (hf_analytic_at z
      (by rwa [Metric.mem_ball, Metric.mem_sphere.mp hz])
      (by intro heq
          rw [heq, Metric.mem_sphere, dist_self] at hz
          linarith)).continuousAt.continuousWithinAt
  have h_const_integral : ∀ r, 0 < r → r ≤ R₀ →
      (∮ z in C(s, r), f z) = (∮ z in C(s, R₀), f z) := fun r hr hr_le =>
    circleIntegral_const_of_meromorphicAt_aux f s rf R₀ hR₀_pos hR₀_lt_rf
      hf_analytic_at r hr hr_le
  apply tendsto_nhds_of_eventually_eq
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Iio_mem_nhds hR₀_pos] with r hr_lt hr_pos
  simp only [Set.mem_Ioi] at hr_pos; simp only [Set.mem_Iio] at hr_lt
  have hf_ci : CircleIntegrable f s r :=
    (hf_cont_sphere r hr_pos (lt_trans hr_lt hR₀_lt_rf)).circleIntegrable hr_pos.le
  have h_no_pole_on_sphere : ∀ p ∈ S0, ∀ z ∈ Metric.sphere s r, z - ↑p ≠ 0 := by
    intro p hp z hz
    apply sub_ne_zero.mpr; intro heq
    rw [heq] at hz
    by_cases h_eq : p = s
    · exact absurd (h_eq ▸ hz) (by simp [(ne_of_gt hr_pos).symm])
    · have h_dist := hδ_sep p hp h_eq
      rw [Metric.mem_sphere] at hz; linarith [lt_trans hr_lt hR₀_lt_δ]
  have hsum_ci : CircleIntegrable (fun z => ∑ s' ∈ S0, residueAt f s' / (z - s')) s r := by
    apply ContinuousOn.circleIntegrable hr_pos.le
    apply continuousOn_finsetSum; intro p hp
    exact ContinuousOn.div continuousOn_const (continuousOn_id.sub continuousOn_const)
      (fun z hz => h_no_pole_on_sphere p hp z hz)
  have h_no_pole_in_cb : ∀ p ∈ S0.erase s,
      ∀ z ∈ Metric.closedBall s r, z - ↑p ≠ 0 := by
    intro p hp z hz
    apply sub_ne_zero.mpr; intro heq
    rw [heq] at hz
    have h_dist := hδ_sep p (Finset.mem_of_mem_erase hp) (Finset.ne_of_mem_erase hp)
    rw [Metric.mem_closedBall] at hz; linarith
  rw [circleIntegral.integral_sub hf_ci hsum_ci,
    circleIntegral_simple_pole_sum S0 (residueAt f) s hs r hr_pos
      h_no_pole_on_sphere h_no_pole_in_cb,
    mul_sub, mul_comm (residueAt f s) _, ← mul_assoc,
    inv_mul_cancel₀ h2piI_ne, one_mul]
  rw [h_const_integral r hr_pos hr_lt.le]
  rw [show residueAt f s = (2 * ↑Real.pi * I)⁻¹ * ∮ z in C(s, R₀), f z from by
    unfold residueAt
    apply Filter.Tendsto.limUnder_eq
    apply tendsto_nhds_of_eventually_eq
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds hR₀_pos] with r' hr'_lt hr'_pos
    simp only [Set.mem_Ioi] at hr'_pos; simp only [Set.mem_Iio] at hr'_lt
    rw [h_const_integral r' hr'_pos hr'_lt.le], sub_self]

/-- Helper: If `g` decomposes as `g = g_reg + g_pol` where:
- `g_reg` is continuous on `γ`'s image with `∮ g_reg = 0`, and
- `g_pol` is ContinuousOn `U \ S0` with `CPV(S0, g_pol, ε) → 0`,
then `CPV(S0, g, ε) → 0`.

The proof splits `CPV(g) = CPV(g_reg) + CPV(g_pol)` using CPV linearity
(both are interval integrable for fixed ε > 0), then combines the limits. -/
private theorem cpv_tendsto_zero_of_add_decomposition
    (U : Set ℂ) (S0 : Finset ℂ) (g g_reg g_pol : ℂ → ℂ)
    (γ : PiecewiseC1Immersion) (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hg_eq : ∀ z, g z = g_reg z + g_pol z)
    (hg_reg_cont : ContinuousOn g_reg (γ.toFun '' Icc γ.a γ.b))
    (hg_reg_int_zero : ∫ t in γ.a..γ.b, g_reg (γ.toFun t) * deriv γ.toFun t = 0)
    (hg_pol_cont : ContinuousOn g_pol (U \ ↑S0))
    (hg_pol_tendsto : Tendsto (fun ε => ∫ t in γ.a..γ.b,
      cauchyPrincipalValueIntegrandOn S0 g_pol γ.toFun ε t) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε => ∫ t in γ.a..γ.b,
      cauchyPrincipalValueIntegrandOn S0 g γ.toFun ε t) (𝓝[>] 0) (𝓝 0) := by
  rw [show (0 : ℂ) = 0 + 0 from (add_zero 0).symm]
  apply Filter.Tendsto.congr' _
    ((tendsto_cpv_of_continuousOn_zero_integral S0 g_reg γ
      hg_reg_cont hg_reg_int_zero).add hg_pol_tendsto)
  filter_upwards [self_mem_nhdsWithin] with ε (hε : (0 : ℝ) < ε)
  simp_rw [funext hg_eq, cpvIntegrandOn_add]
  exact (intervalIntegral.integral_add
    (intervalIntegrable_cauchyPrincipalValueIntegrandOn (S0 := S0) hε hg_reg_cont)
    (intervalIntegrable_cpvIntegrandOn_of_continuousOn_diff U S0 g_pol
      hg_pol_cont γ hγ_in_U ε hε)).symm

end GeneralizedResidueTheory
