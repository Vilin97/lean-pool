/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.GeneralizedResidueTheory.Homotopy.Integrality
import LeanPool.LeanModularForms.GeneralizedResidueTheory.Homotopy.ParametricDiff

/-!
# Homotopy Invariance of Winding Numbers

Homotopy invariance for generalized winding numbers (both piecewise C¹ and
smooth), plus the classical winding number formula for curves avoiding a point.

## Main Results

* `windingNumber_eq_of_piecewise_homotopic` — winding number invariant
    under piecewise homotopy
* `windingNumber_eq_of_homotopic_closed` — winding number invariant
    under smooth homotopy
* `generalizedWindingNumber_eq_classical_away` — PV winding number
    equals classical integral when curve avoids z₀
* `contourIntegral_eq_of_homotopic` — contour integrals equal under
    homotopy for holomorphic integrands
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

private theorem homotopy_uniform_avoidance
    (H : ℝ × ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (hab : a < b)
    (hH_cont : Continuous H)
    (hH_avoid : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0 : ℝ) 1,
      H (t, s) ≠ z₀) :
    ∃ δ > 0, ∀ t ∈ Icc a b, ∀ s ∈ Icc (0 : ℝ) 1,
      δ ≤ ‖H (t, s) - z₀‖ := by
  have hcompact : IsCompact (H '' (Icc a b ×ˢ Icc (0 : ℝ) 1)) :=
    (isCompact_Icc.prod isCompact_Icc).image hH_cont
  have hnonempty : (H '' (Icc a b ×ˢ Icc (0 : ℝ) 1)).Nonempty :=
    ⟨H (a, 0), (a, 0),
      ⟨left_mem_Icc.mpr (hab.le),
       left_mem_Icc.mpr zero_le_one⟩, rfl⟩
  have hz_notin : z₀ ∉ H '' (Icc a b ×ˢ Icc (0 : ℝ) 1) :=
    fun ⟨⟨t, s⟩, ⟨ht, hs⟩, heq⟩ =>
      hH_avoid t ht s hs heq
  have hδ := (hcompact.isClosed.notMem_iff_infDist_pos
    hnonempty).mp hz_notin
  refine ⟨_, hδ, fun t ht s hs => ?_⟩
  have hmem : H (t, s) ∈ H '' (Icc a b ×ˢ Icc (0 : ℝ) 1) :=
    ⟨(t, s), ⟨ht, hs⟩, rfl⟩
  calc Metric.infDist z₀ _ ≤ dist z₀ (H (t, s)) :=
        Metric.infDist_le_dist_of_mem hmem
    _ = ‖H (t, s) - z₀‖ := by
        rw [Complex.dist_eq, norm_sub_rev]

private lemma homotopy_integrand_continuousOn_t
    {H : ℝ × ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {P : Finset ℝ}
    (hH_cont : Continuous H)
    (hH_avoid : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0 : ℝ) 1, H (t, s) ≠ z₀)
    (hH_deriv_cont : ∀ p₁ p₂ : ℝ, p₁ < p₂ →
      (∀ t ∈ Ioo p₁ p₂, t ∉ P) → Ioo p₁ p₂ ⊆ Ioo a b →
      ContinuousOn (fun (p : ℝ × ℝ) => deriv (fun t' => H (t', p.2)) p.1)
        (Ioo p₁ p₂ ×ˢ Icc 0 1))
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    let f := fun t s => (H (t, s) - z₀)⁻¹ * deriv (fun t' => H (t', s)) t
    let P' : Finset ℝ := P ∪ {a, b}
    ContinuousOn (fun t => f t s) ((Icc a b) \ P') := by
  intro f P' t ⟨ht_Icc, ht_notP'⟩
  simp only [P', Finset.coe_union, Finset.coe_pair, Set.mem_union,
    Set.mem_insert_iff, not_or] at ht_notP'
  have ht_Ioo : t ∈ Ioo a b :=
    ⟨lt_of_le_of_ne ht_Icc.1 (Ne.symm ht_notP'.2.1),
     lt_of_le_of_ne ht_Icc.2 ht_notP'.2.2⟩
  obtain ⟨ε, hε_pos, hε_avoid⟩ := exists_ball_avoiding_finset ht_notP'.1
  set ε' := min (ε / 2) (min (t - a) (b - t)) with hε'_def
  have hε'_pos : 0 < ε' := by
    simp only [hε'_def, lt_min_iff]
    exact ⟨by linarith, sub_pos.mpr ht_Ioo.1, sub_pos.mpr ht_Ioo.2⟩
  have hε'_le : ε' ≤ ε / 2 := min_le_left _ _
  have h_avoid_P : ∀ t' ∈ Ioo (t - ε') (t + ε'), t' ∉ P := fun t' ht' =>
    hε_avoid t' ⟨by linarith [ht'.1], by linarith [ht'.2]⟩
  have ht_in : t ∈ Ioo (t - ε') (t + ε') := ⟨by linarith, by linarith⟩
  have h_sub_ab : Ioo (t - ε') (t + ε') ⊆ Ioo a b := by
    intro x hx
    have h1 := (min_le_right (ε / 2) _).trans (min_le_left (t - a) (b - t))
    have h2 := (min_le_right (ε / 2) _).trans (min_le_right (t - a) (b - t))
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  apply ContinuousWithinAt.mono _ (Set.sdiff_subset_sdiff_right (Finset.coe_subset.mpr
    (Finset.subset_union_left (s₂ := {a, b}))))
  exact ContinuousWithinAt.mul
    ((hH_cont.comp (continuous_id.prodMk continuous_const)).continuousAt.sub
      continuousAt_const |>.inv₀ (sub_ne_zero.mpr (hH_avoid t ht_Icc s hs)) |>.continuousWithinAt)
    (((hH_deriv_cont _ _ (by linarith : t - ε' < t + ε') h_avoid_P h_sub_ab).comp
      (continuous_id.prodMk continuous_const).continuousOn
      (fun t' ht' => ⟨ht', hs⟩) t ht_in).continuousAt
      (Ioo_mem_nhds ht_in.1 ht_in.2) |>.continuousWithinAt)

private lemma homotopy_integrand_continuousWithinAt_s
    {H : ℝ × ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {P : Finset ℝ}
    (_hab : a < b)
    (hH_cont : Continuous H)
    (hH_avoid : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0 : ℝ) 1, H (t, s) ≠ z₀)
    (hH_deriv_cont : ∀ p₁ p₂ : ℝ, p₁ < p₂ →
      (∀ t ∈ Ioo p₁ p₂, t ∉ P) → Ioo p₁ p₂ ⊆ Ioo a b →
      ContinuousOn (fun (p : ℝ × ℝ) => deriv (fun t' => H (t', p.2)) p.1)
        (Ioo p₁ p₂ ×ˢ Icc 0 1))
    {s₀ : ℝ} (hs₀ : s₀ ∈ Icc (0 : ℝ) 1)
    {t : ℝ} (ht_Icc : t ∈ Icc a b) (ht_Ioo : t ∈ Ioo a b) (ht_notP : t ∉ P) :
    let f := fun t s => (H (t, s) - z₀)⁻¹ * deriv (fun t' => H (t', s)) t
    ContinuousWithinAt (fun s => f t s) (Icc 0 1) s₀ := by
  intro f
  obtain ⟨ε, hε_pos, hε_avoid⟩ := exists_ball_avoiding_finset ht_notP
  set ε' := min (ε / 2) (min (t - a) (b - t)) with hε'_def
  have hε'_pos : 0 < ε' := by
    simp only [hε'_def, lt_min_iff]
    exact ⟨by linarith, sub_pos.mpr ht_Ioo.1, sub_pos.mpr ht_Ioo.2⟩
  have hε'_le : ε' ≤ ε / 2 := min_le_left _ _
  have h_avoid_P : ∀ t' ∈ Ioo (t - ε') (t + ε'), t' ∉ P := fun t' ht' =>
    hε_avoid t' ⟨by linarith [ht'.1], by linarith [ht'.2]⟩
  have ht_in : t ∈ Ioo (t - ε') (t + ε') := ⟨by linarith, by linarith⟩
  have h_sub_ab : Ioo (t - ε') (t + ε') ⊆ Ioo a b := by
    intro x hx
    have h1 := (min_le_right (ε / 2) _).trans (min_le_left (t - a) (b - t))
    have h2 := (min_le_right (ε / 2) _).trans (min_le_right (t - a) (b - t))
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  exact ContinuousWithinAt.mul
    ((hH_cont.comp (continuous_const.prodMk continuous_id)).continuousAt.sub
      continuousAt_const |>.inv₀
        (sub_ne_zero.mpr (hH_avoid t ht_Icc s₀ hs₀))
      |>.continuousWithinAt)
    (((hH_deriv_cont _ _ (by linarith : t - ε' < t + ε') h_avoid_P h_sub_ab).comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs => ⟨ht_in, hs⟩)) s₀ hs₀)

private lemma homotopy_pv_eq_integral
    {H : ℝ × ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {δ : ℝ}
    (hab : a < b) (hδ_pos : 0 < δ)
    (hδ_bound : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0 : ℝ) 1, δ ≤ ‖H (t, s) - z₀‖)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    let f := fun t s => (H (t, s) - z₀)⁻¹ * deriv (fun t' => H (t', s)) t
    generalizedWindingNumber' (fun t => H (t, s)) a b z₀ =
    (2 * Real.pi * I)⁻¹ * ∫ t in a..b, f t s := by
  intro f
  unfold generalizedWindingNumber' cauchyPrincipalValue'
  simp only [sub_zero]; congr 1
  apply limUnder_eventually_eq_const
  filter_upwards [Ioo_mem_nhdsGT hδ_pos] with ε hε
  apply intervalIntegral.integral_congr_ae
  filter_upwards with t ht
  have ht' : t ∈ Icc a b := by
    rw [Set.uIoc_of_le hab.le] at ht; exact Ioc_subset_Icc_self ht
  simp only [f, ((mem_Ioo.mp hε).2.trans_le (hδ_bound t ht' s hs)), ↓reduceIte, deriv_sub_const]

private lemma homotopy_piecewise_aestronglyMeasurable
    {H : ℝ × ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {P : Finset ℝ}
    (hH_cont : Continuous H)
    (hH_avoid : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0 : ℝ) 1, H (t, s) ≠ z₀)
    (hH_deriv_cont : ∀ p₁ p₂ : ℝ, p₁ < p₂ →
      (∀ t ∈ Ioo p₁ p₂, t ∉ P) → Ioo p₁ p₂ ⊆ Ioo a b →
      ContinuousOn (fun (p : ℝ × ℝ) => deriv (fun t' => H (t', p.2)) p.1)
        (Ioo p₁ p₂ ×ˢ Icc 0 1))
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    let f := fun t s => (H (t, s) - z₀)⁻¹ * deriv (fun t' => H (t', s)) t
    AEStronglyMeasurable (fun t => f t s) (volume.restrict (Icc a b)) := by
  intro f
  let P' : Finset ℝ := P ∪ {a, b}
  have hf_cont_off_P' : ContinuousOn (fun t => f t s) ((Icc a b) \ P') :=
    homotopy_integrand_continuousOn_t hH_cont hH_avoid hH_deriv_cont hs
  have h_union : Icc a b = (Icc a b \ (P' : Set ℝ)) ∪ ((P' : Set ℝ) ∩ Icc a b) := by
    ext x; simp [and_comm]; tauto
  rw [h_union, aestronglyMeasurable_union_iff]
  constructor
  · exact hf_cont_off_P'.aestronglyMeasurable
      (measurableSet_Icc.diff (Finset.measurableSet P'))
  · have h_null : volume ((P' : Set ℝ) ∩ Icc a b) = 0 :=
      (Finset.finite_toSet P' |>.inter_of_left (Icc a b)).measure_zero _
    rw [Measure.restrict_zero_set h_null]
    exact aestronglyMeasurable_zero_measure _

private theorem windingNumber_continuousOn_param_piecewise_with_bound
    {H : ℝ × ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {P : Finset ℝ} {M : ℝ} (hab : a < b)
    (hH_cont : Continuous H)
    (hH_avoid : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0 : ℝ) 1, H (t, s) ≠ z₀)
    (_hH_diff : ∀ t ∈ Ioo a b, t ∉ P → ∀ s ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (fun t' => H (t', s)) t)
    (hH_deriv_cont : ∀ p₁ p₂ : ℝ, p₁ < p₂ →
      (∀ t ∈ Ioo p₁ p₂, t ∉ P) → Ioo p₁ p₂ ⊆ Ioo a b →
      ContinuousOn (fun (p : ℝ × ℝ) => deriv (fun t' => H (t', p.2)) p.1)
        (Ioo p₁ p₂ ×ˢ Icc 0 1))
    (hM_bound : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖deriv (fun t' => H (t', s)) t‖ ≤ M) :
    ContinuousOn (fun s => generalizedWindingNumber' (fun t => H (t, s)) a b z₀) (Icc 0 1) := by
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := homotopy_uniform_avoidance H a b z₀ hab hH_cont hH_avoid
  let f : ℝ → ℝ → ℂ := fun t s => (H (t, s) - z₀)⁻¹ * deriv (fun t' => H (t', s)) t
  have hf_bound : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc a b,
      ‖f t s‖ ≤ M / δ := fun s hs t ht =>
    winding_integrand_bounded_of_uniform_avoidance
      hδ_pos hδ_bound hM_bound t ht s hs
  have h_pv := fun s hs => homotopy_pv_eq_integral hab hδ_pos hδ_bound s hs
  intro s₀ hs₀
  apply ContinuousWithinAt.congr_of_eventuallyEq _
    (eventually_of_mem self_mem_nhdsWithin h_pv) (h_pv s₀ hs₀)
  apply continuousWithinAt_const.mul
  apply continuousWithinAt_integral_of_dominated_piecewise (M := M / δ) hab.le
  · exact fun s hs => homotopy_piecewise_aestronglyMeasurable hH_cont hH_avoid hH_deriv_cont s hs
  · exact fun s hs t ht => hf_bound s hs t ht
  · let B : Set ℝ := {a, b} ∪ (P : Set ℝ)
    have hB_null : volume B = 0 :=
      ((Set.finite_insert.mpr (Set.finite_singleton b)).union
        (Finset.finite_toSet P)).measure_zero _
    have h_cont_off_B : ∀ t ∈ Icc a b, t ∉ B →
        ContinuousWithinAt (fun s => f t s) (Icc 0 1) s₀ := by
      intro t ht_Icc ht_notB
      simp only [B, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht_notB
      have ht_Ioo : t ∈ Ioo a b :=
        ⟨lt_of_le_of_ne ht_Icc.1 (Ne.symm ht_notB.1.1),
         lt_of_le_of_ne ht_Icc.2 ht_notB.1.2⟩
      exact homotopy_integrand_continuousWithinAt_s hab hH_cont hH_avoid hH_deriv_cont
        hs₀ ht_Icc ht_Ioo ht_notB.2
    have h_ae_not_B : ∀ᵐ t ∂(volume.restrict (Icc a b)), t ∉ B := by
      rw [ae_restrict_iff' measurableSet_Icc, ae_iff]
      simp only [Set.setOf_and, Classical.not_imp, not_not]
      exact measure_mono_null Set.inter_subset_right hB_null
    filter_upwards [h_ae_not_B, ae_restrict_mem measurableSet_Icc] with t ht_notB ht_Icc
    exact h_cont_off_B t ht_Icc ht_notB

private theorem continuous_integer_valued_constant
    (f : ℝ → ℂ) (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf_int : ∀ s ∈ Icc (0 : ℝ) 1, ∃ n : ℤ, f s = n) :
    f 0 = f 1 := by
  let g : Icc (0 : ℝ) 1 → ℂ := fun x => f x.val
  have hg_loc : IsLocallyConstant g := by
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro y
    by_cases hy : ∃ n : ℤ, y = n
    · obtain ⟨n, rfl⟩ := hy
      have heq : g ⁻¹' {↑n} =
          g ⁻¹' (Metric.ball (n : ℂ) 1) := by
        ext ⟨x, hx⟩
        simp only [g, mem_preimage, mem_singleton_iff,
          Metric.mem_ball]
        constructor
        · intro heq; rw [heq]; simp only [dist_self, zero_lt_one]
        · intro hdist
          obtain ⟨m, hm⟩ := hf_int x hx
          rw [hm] at hdist ⊢
          have h1 : dist (m : ℂ) (n : ℂ) < 1 := hdist
          rw [Complex.dist_eq, show (m : ℂ) - (n : ℂ) =
            ((m - n : ℤ) : ℂ) from by push_cast; ring,
            Complex.norm_intCast, ← Int.cast_abs] at h1
          have h2 : |m - n| < 1 := by exact_mod_cast h1
          have h3 : m - n = 0 := Int.abs_lt_one_iff.mp h2
          have h4 : m = n := sub_eq_zero.mp h3
          exact_mod_cast h4
      rw [heq]
      exact hf_cont.restrict.isOpen_preimage _ Metric.isOpen_ball
    · convert isOpen_empty
      ext ⟨x, hx⟩
      simp only [g, mem_preimage, mem_singleton_iff,
        mem_empty_iff_false, iff_false]
      intro heq
      obtain ⟨n, hn⟩ := hf_int x hx
      exact hy ⟨n, heq.symm.trans hn⟩
  have h0 : (⟨0, left_mem_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1)⟩ :
      Icc (0 : ℝ) 1) ∈ (Set.univ : Set (Icc (0 : ℝ) 1)) := trivial
  have h1 : (⟨1, right_mem_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1)⟩ :
      Icc (0 : ℝ) 1) ∈ (Set.univ : Set (Icc (0 : ℝ) 1)) := trivial
  exact hg_loc.apply_eq_of_isPreconnected
    isPreconnected_univ h0 h1

private theorem generalizedWindingNumber'_eq_of_eq_on
    (f g : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (hab : a < b)
    (heq_val : ∀ t ∈ Icc a b, f t = g t)
    (heq_deriv : ∀ᵐ t ∂volume.restrict (Set.uIoc a b),
      deriv f t = deriv g t) :
    generalizedWindingNumber' f a b z₀ =
    generalizedWindingNumber' g a b z₀ := by
  unfold generalizedWindingNumber' cauchyPrincipalValue'
  simp only [sub_zero, deriv_sub_const]
  have h_fun_eq :
      (fun ε => ∫ t in a..b,
        if ‖f t - z₀‖ > ε then
          (f t - z₀)⁻¹ * deriv f t else 0) =
      (fun ε => ∫ t in a..b,
        if ‖g t - z₀‖ > ε then
          (g t - z₀)⁻¹ * deriv g t else 0) := by
    funext ε
    apply intervalIntegral.integral_congr_ae
    have h_uIoc : Set.uIoc a b = Ioc a b :=
      Set.uIoc_of_le (hab.le)
    rw [h_uIoc]
    rw [h_uIoc] at heq_deriv
    have h_ae : ∀ᵐ t ∂volume.restrict (Ioc a b),
        deriv f t = deriv g t := heq_deriv
    rw [ae_restrict_iff' measurableSet_Ioc] at h_ae
    filter_upwards [h_ae] with t ht ht_mem
    simp only [ht ht_mem,
      heq_val t (Ioc_subset_Icc_self ht_mem)]
  rw [h_fun_eq]

/-- Winding number is invariant under piecewise C¹ homotopy. -/
theorem windingNumber_eq_of_piecewise_homotopic
    (γ₀ γ₁ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ)
    (P : Finset ℝ) (hab : a < b)
    (hhom : PiecewiseCurvesHomotopicAvoiding
      γ₀ γ₁ a b z₀ P) :
    generalizedWindingNumber' γ₀ a b z₀ =
    generalizedWindingNumber' γ₁ a b z₀ := by
  obtain ⟨H, hH_cont, hH0, hH1, hH_closed, hH_avoid, hH_diff, hH_deriv_cont,
    M, hM_bound⟩ := hhom
  let n : ℝ → ℂ := fun s => generalizedWindingNumber' (fun t => H (t, s)) a b z₀
  have hn_cont : ContinuousOn n (Icc 0 1) :=
    windingNumber_continuousOn_param_piecewise_with_bound hab hH_cont hH_avoid
      hH_diff hH_deriv_cont hM_bound
  have hn_int : ∀ s ∈ Icc (0 : ℝ) 1, ∃ m : ℤ, n s = m := by
    intro s hs
    apply windingNumber_integer_of_piecewise_closed_avoiding (fun t => H (t, s)) a b z₀ P hab
    · exact hH_closed s hs
    · exact hH_cont.comp (continuous_id.prodMk continuous_const) |>.continuousOn
    · intro t ht h_not_P
      exact hH_diff t ht h_not_P s hs
    · intro p₁ p₂ hp₁p₂ hpiece h_sub
      convert (hH_deriv_cont p₁ p₂ hp₁p₂ hpiece h_sub).comp
        (continuous_id.prodMk continuous_const).continuousOn
        (fun t (ht : t ∈ Ioo p₁ p₂) => (show (t, s) ∈ Ioo p₁ p₂ ×ˢ Icc 0 1 from ⟨ht, hs⟩))
        using 1
      rfl
    · exact fun t ht => hH_avoid t ht s hs
    · exact ⟨M, fun t ht => hM_bound t ht s hs⟩
  have heq : n 0 = n 1 := continuous_integer_valued_constant n hn_cont hn_int
  have hn0_eq : n 0 = generalizedWindingNumber' γ₀ a b z₀ := by
    apply generalizedWindingNumber'_eq_of_eq_on (fun t => H (t, 0)) γ₀ a b z₀ hab hH0
    rw [Set.uIoc_of_le (hab.le)]
    have h_eq_on_Ioo : Set.EqOn (fun t => H (t, 0)) γ₀ (Ioo a b) :=
      fun t' ht' => hH0 t' (Ioo_subset_Icc_self ht')
    have h_deriv_eq_on : Set.EqOn (deriv (fun t => H (t, 0))) (deriv γ₀) (Ioo a b) :=
      h_eq_on_Ioo.deriv isOpen_Ioo
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [Ioo_ae_eq_Ioc.mem_iff] with t ht ht_Ioc
    exact h_deriv_eq_on (ht.mpr ht_Ioc)
  have hn1_eq : n 1 = generalizedWindingNumber' γ₁ a b z₀ := by
    apply generalizedWindingNumber'_eq_of_eq_on (fun t => H (t, 1)) γ₁ a b z₀ hab hH1
    rw [Set.uIoc_of_le (hab.le)]
    have h_eq_on_Ioo : Set.EqOn (fun t => H (t, 1)) γ₁ (Ioo a b) :=
      fun t' ht' => hH1 t' (Ioo_subset_Icc_self ht')
    have h_deriv_eq_on : Set.EqOn (deriv (fun t => H (t, 1))) (deriv γ₁) (Ioo a b) :=
      h_eq_on_Ioo.deriv isOpen_Ioo
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [Ioo_ae_eq_Ioc.mem_iff] with t ht ht_Ioc
    exact h_deriv_eq_on (ht.mpr ht_Ioc)
  rw [← hn0_eq, ← hn1_eq, heq]

private lemma smooth_winding_pv_eq_integral
    {γ : ℝ × ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {δ : ℝ}
    (hab : a < b) (hδ_pos : 0 < δ)
    (hδ_bound : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ (t, s) - z₀‖)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    let f := fun t s => (γ (t, s) - z₀)⁻¹ * deriv (fun t' => γ (t', s)) t
    generalizedWindingNumber' (fun t => γ (t, s)) a b z₀ =
    (2 * Real.pi * I)⁻¹ * ∫ t in a..b, f t s := by
  intro f
  unfold generalizedWindingNumber' cauchyPrincipalValue'
  simp only [sub_zero]; congr 1
  apply limUnder_eventually_eq_const
  filter_upwards [Ioo_mem_nhdsGT hδ_pos] with ε hε
  apply intervalIntegral.integral_congr_ae
  filter_upwards with t ht
  have ht' : t ∈ Icc a b := by
    rw [Set.uIoc_of_le hab.le] at ht; exact Ioc_subset_Icc_self ht
  simp only [f, ((mem_Ioo.mp hε).2.trans_le (hδ_bound t ht' s hs)), ↓reduceIte, deriv_sub_const]

private lemma smooth_winding_integral_continuousOn
    {γ : ℝ × ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {M : ℝ}
    (hab : a < b)
    (hγ_cont : Continuous γ)
    (hγ_avoid : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0 : ℝ) 1, γ (t, s) ≠ z₀)
    (hγ_deriv_cont : Continuous (fun p : ℝ × ℝ => deriv (fun t' => γ (t', p.2)) p.1))
    (hM : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖(γ (t, s) - z₀)⁻¹ * deriv (fun t' => γ (t', s)) t‖ ≤ M) :
    let f := fun t s => (γ (t, s) - z₀)⁻¹ * deriv (fun t' => γ (t', s)) t
    ContinuousOn (fun s => ∫ t in a..b, f t s) (Icc 0 1) := by
  intro f s₁ hs₁
  apply intervalIntegral.continuousWithinAt_of_dominated_interval (bound := fun _ => M)
  · apply eventually_of_mem self_mem_nhdsWithin
    intro s hs
    have hab' : Icc a b = Icc (min a b) (max a b) := by
      simp [min_eq_left hab.le, max_eq_right hab.le]
    apply (ContinuousOn.mul
      (ContinuousOn.inv₀
        ((hγ_cont.comp (continuous_id.prodMk continuous_const)).sub
          continuous_const).continuousOn
        (fun t ht => by simp only [ne_eq, sub_eq_zero]; exact hγ_avoid t (hab' ▸ ht) s hs))
      (hγ_deriv_cont.comp (continuous_id.prodMk continuous_const)).continuousOn
      |>.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · apply eventually_of_mem self_mem_nhdsWithin
    intro s hs; filter_upwards with t ht
    rw [Set.uIoc_of_le hab.le] at ht; exact hM t (Ioc_subset_Icc_self ht) s hs
  · exact intervalIntegrable_const
  · filter_upwards with t ht
    apply ContinuousAt.continuousWithinAt
    exact ContinuousAt.mul
      ((hγ_cont.comp (continuous_const.prodMk continuous_id)).sub continuous_const
        |>.continuousAt |>.inv₀ (by
        simp only [ne_eq, sub_eq_zero]
        rw [Set.uIoc_of_le hab.le] at ht
        exact hγ_avoid t (Ioc_subset_Icc_self ht) s₁ hs₁))
      (hγ_deriv_cont.comp (continuous_const.prodMk continuous_id) |>.continuousAt)

private theorem windingNumber_continuous_in_param
    (γ : ℝ × ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (hab : a < b)
    (hγ_cont : Continuous γ)
    (hγ_avoid : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0 : ℝ) 1, γ (t, s) ≠ z₀)
    (hγ_deriv_cont : Continuous (fun p : ℝ × ℝ =>
      deriv (fun t' => γ (t', p.2)) p.1)) :
    ContinuousOn (fun s =>
      generalizedWindingNumber' (fun t => γ (t, s)) a b z₀) (Icc 0 1) := by
  obtain ⟨δ, hδ_pos, hδ_bound⟩ :=
    homotopy_uniform_avoidance γ a b z₀ hab hγ_cont hγ_avoid
  let f : ℝ → ℝ → ℂ := fun t s =>
    (γ (t, s) - z₀)⁻¹ * deriv (fun t' => γ (t', s)) t
  have hf_cont_on : ContinuousOn
      (fun p : ℝ × ℝ => f p.1 p.2) (Icc a b ×ˢ Icc 0 1) :=
    ContinuousOn.mul
      (ContinuousOn.inv₀
        (hγ_cont.sub continuous_const).continuousOn
        (fun ⟨t, s⟩ ⟨ht, hs⟩ => by
          simp only [ne_eq, sub_eq_zero]; exact hγ_avoid t ht s hs))
      hγ_deriv_cont.continuousOn
  obtain ⟨M, hM⟩ : ∃ M, ∀ t ∈ Icc a b, ∀ s ∈ Icc (0 : ℝ) 1, ‖f t s‖ ≤ M := by
    obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hf_cont_on
    exact ⟨M, fun t ht s hs => hM (t, s) ⟨ht, hs⟩⟩
  have h_pv := fun s hs => smooth_winding_pv_eq_integral hab hδ_pos hδ_bound s hs
  intro s₀ hs₀
  apply ContinuousWithinAt.congr_of_eventuallyEq _
    (eventually_of_mem self_mem_nhdsWithin h_pv) (h_pv s₀ hs₀)
  exact continuousWithinAt_const.mul
    ((smooth_winding_integral_continuousOn hab hγ_cont hγ_avoid
      hγ_deriv_cont hM).continuousWithinAt hs₀)

/-- Winding number is invariant under smooth homotopy. -/
theorem windingNumber_eq_of_homotopic_closed
    (γ₀ γ₁ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ)
    (hab : a < b)
    (hhom : ClosedCurvesHomotopicAvoiding
      γ₀ γ₁ a b z₀) :
    generalizedWindingNumber' γ₀ a b z₀ =
    generalizedWindingNumber' γ₁ a b z₀ := by
  obtain ⟨H, hH_cont, hH0, hH1, hH_closed, hH_avoid,
    hH_diff_t, hH_deriv_cont⟩ := hhom
  let n : ℝ → ℂ := fun s =>
    generalizedWindingNumber' (fun t => H (t, s)) a b z₀
  have hn_int :
      ∀ s ∈ Icc (0 : ℝ) 1, ∃ m : ℤ, n s = m := by
    intro s hs
    apply windingNumber_integer_of_closed_avoiding
      (fun t => H (t, s)) a b z₀ hab
    · exact hH_closed s hs
    · exact hH_cont.comp
        (continuous_id.prodMk continuous_const)
        |>.continuousOn
    · exact fun t ht => hH_diff_t t ht s hs
    · exact hH_deriv_cont.comp
        (continuous_id.prodMk continuous_const)
        |>.continuousOn
    · exact fun t ht => hH_avoid t ht s hs
  have hn_cont : ContinuousOn n (Icc 0 1) :=
    windingNumber_continuous_in_param H a b z₀ hab
      hH_cont hH_avoid hH_deriv_cont
  have heq : n 0 = n 1 :=
    continuous_integer_valued_constant n hn_cont hn_int
  have hn0_eq : n 0 = generalizedWindingNumber' γ₀ a b z₀ := by
    apply generalizedWindingNumber'_eq_of_eq_on
      (fun t => H (t, 0)) γ₀ a b z₀ hab hH0
    rw [Set.uIoc_of_le (hab.le)]
    have h_eq_on_Ioo :
        Set.EqOn (fun t => H (t, 0)) γ₀ (Ioo a b) :=
      fun t' ht' => hH0 t' (Ioo_subset_Icc_self ht')
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [Ioo_ae_eq_Ioc.mem_iff] with t ht ht_Ioc
    exact (h_eq_on_Ioo.deriv isOpen_Ioo) (ht.mpr ht_Ioc)
  have hn1_eq : n 1 = generalizedWindingNumber' γ₁ a b z₀ := by
    apply generalizedWindingNumber'_eq_of_eq_on
      (fun t => H (t, 1)) γ₁ a b z₀ hab hH1
    rw [Set.uIoc_of_le (hab.le)]
    have h_eq_on_Ioo :
        Set.EqOn (fun t => H (t, 1)) γ₁ (Ioo a b) :=
      fun t' ht' => hH1 t' (Ioo_subset_Icc_self ht')
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [Ioo_ae_eq_Ioc.mem_iff] with t ht ht_Ioc
    exact (h_eq_on_Ioo.deriv isOpen_Ioo) (ht.mpr ht_Ioc)
  rw [← hn0_eq, ← hn1_eq, heq]

/-- When γ avoids z₀, the PV winding number equals the
classical contour integral. -/
theorem generalizedWindingNumber_eq_classical_away
    (γ : PiecewiseC1Curve) (z₀ : ℂ)
    (hoff : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ z₀) :
    generalizedWindingNumber' γ.toFun γ.a γ.b z₀ =
    (2 * Real.pi * I)⁻¹ *
      ∫ t in γ.a..γ.b,
        (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t := by
  unfold generalizedWindingNumber' cauchyPrincipalValue'
  have hcompact : IsCompact (γ.toFun '' Icc γ.a γ.b) :=
    isCompact_Icc.image_of_continuousOn γ.continuous_toFun
  have hnonempty : (γ.toFun '' Icc γ.a γ.b).Nonempty :=
    Set.image_nonempty.mpr (Set.nonempty_Icc.mpr (le_of_lt γ.hab))
  have hz₀_notin : z₀ ∉ γ.toFun '' Icc γ.a γ.b :=
    fun ⟨t, ht, htw⟩ => hoff t ht htw
  have hδ : 0 < Metric.infDist z₀ (γ.toFun '' Icc γ.a γ.b) :=
    (hcompact.isClosed.notMem_iff_infDist_pos hnonempty).mp hz₀_notin
  have h_cutoff_trivial : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ t ∈ Icc γ.a γ.b, ε < ‖γ.toFun t - z₀‖ := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε t ht
    have hmem : γ.toFun t ∈ γ.toFun '' Icc γ.a γ.b := mem_image_of_mem γ.toFun ht
    calc ε < Metric.infDist z₀ (γ.toFun '' Icc γ.a γ.b) := (mem_Ioo.mp hε).2
      _ ≤ dist z₀ (γ.toFun t) := Metric.infDist_le_dist_of_mem hmem
      _ = ‖γ.toFun t - z₀‖ := by rw [Complex.dist_eq, norm_sub_rev]
  congr 1
  apply limUnder_eventually_eq_const
  filter_upwards [h_cutoff_trivial] with ε hε
  apply intervalIntegral.integral_congr_ae
  filter_upwards with t
  intro ht
  simp only [sub_zero]
  have ht' : t ∈ Icc γ.a γ.b := by
    rw [Set.uIoc_of_le (le_of_lt γ.hab)] at ht
    exact Ioc_subset_Icc_self ht
  have h_cond : ε < ‖γ.toFun t - z₀‖ := hε t ht'
  simp only [h_cond, ↓reduceIte, deriv_sub_const]

private lemma integral_congr_homotopy_endpoint
    {f : ℂ → ℂ} {γ : ℝ → ℂ} {H : ℝ × ℝ → ℂ} {a b : ℝ} {s : ℝ}
    (hab : a < b)
    (hHs : ∀ t ∈ Icc a b, H (t, s) = γ t) :
    ∫ t in a..b, f (γ t) * deriv γ t =
    ∫ t in a..b, f (H (t, s)) * deriv (fun t => H (t, s)) t := by
  apply intervalIntegral.integral_congr_ae
  have h_eq : Set.EqOn (fun t => H (t, s)) γ (Ioo a b) :=
    fun t' ht' => hHs t' (Ioo_subset_Icc_self ht')
  simp only [Set.uIoc_of_le hab.le]
  filter_upwards [Ioo_ae_eq_Ioc.mem_iff] with t ht ht_Ioc
  have ht_Ioo : t ∈ Ioo a b := ht.mpr ht_Ioc
  rw [hHs t (Ioo_subset_Icc_self ht_Ioo), (h_eq.deriv isOpen_Ioo) ht_Ioo]

/-- Contour integrals of a holomorphic function are equal
along homotopic curves. -/
theorem contourIntegral_eq_of_homotopic
    (f : ℂ → ℂ) (γ₀ γ₁ : ℝ → ℂ) (a b : ℝ)
    (hab : a < b)
    (_hγ₀_cont : ContinuousOn γ₀ (Icc a b))
    (_hγ₁_cont : ContinuousOn γ₁ (Icc a b))
    (_hγ₀_diff : ∀ t ∈ Ioo a b,
      DifferentiableAt ℝ γ₀ t)
    (_hγ₁_diff : ∀ t ∈ Ioo a b,
      DifferentiableAt ℝ γ₁ t)
    (H : ℝ × ℝ → ℂ) (_hH_cont : Continuous H)
    (hH0 : ∀ t ∈ Icc a b, H (t, 0) = γ₀ t)
    (hH1 : ∀ t ∈ Icc a b, H (t, 1) = γ₁ t)
    (_hH_ends : ∀ s ∈ Icc (0 : ℝ) 1,
      H (a, s) = γ₀ a ∧ H (b, s) = γ₀ b)
    (hf_holo : ∀ t ∈ Icc a b,
      ∀ s ∈ Icc (0 : ℝ) 1,
        DifferentiableAt ℂ f (H (t, s)))
    (hfH_cont : Continuous (f ∘ H))
    (hH_smooth : ContDiff ℝ 2 H)
    (hH_deriv_s_zero_at_ends :
      ∀ s ∈ Icc (0 : ℝ) 1,
        deriv (fun s' => H (a, s')) s = 0 ∧
        deriv (fun s' => H (b, s')) s = 0)
    (hf_differentiable : Differentiable ℂ f) :
    ∫ t in a..b, f (γ₀ t) * deriv γ₀ t =
    ∫ t in a..b, f (γ₁ t) * deriv γ₁ t := by
  rw [integral_congr_homotopy_endpoint hab hH0,
      integral_congr_homotopy_endpoint hab hH1]
  let I : ℝ → ℂ := fun s =>
    ∫ t in a..b, f (H (t, s)) *
      deriv (fun t' => H (t', s)) t
  suffices h : I 0 = I 1 from h
  have hH_diff : Differentiable ℝ H :=
    hH_smooth.differentiable
      (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have h_deriv_t_cont : Continuous
      (fun p : ℝ × ℝ =>
        deriv (fun t => H (t, p.2)) p.1) :=
    (contDiff_partialDeriv_fst_of_contDiff_two
      H hH_smooth).continuous
  have h_integrand_cont : Continuous
      (fun p : ℝ × ℝ => f (H p) *
        deriv (fun t => H (t, p.2)) p.1) :=
    hfH_cont.mul h_deriv_t_cont
  have hI_cont : ContinuousOn I (Icc 0 1) :=
    intervalIntegral_continuous_on_param
      (fun t s => f (H (t, s)) *
        deriv (fun t' => H (t', s)) t)
      a b (Icc 0 1) (hab.le) h_integrand_cont
      (fun s _ => by
        apply Continuous.intervalIntegrable
        exact h_integrand_cont.comp
          (continuous_id.prodMk continuous_const))
  have hI_deriv_zero : ∀ s ∈ Ico (0 : ℝ) 1,
      HasDerivWithinAt I 0 (Ici s) s := by
    intro s ⟨hs_ge, hs_lt⟩
    have hs : s ∈ Icc (0 : ℝ) 1 := ⟨hs_ge, le_of_lt hs_lt⟩
    obtain ⟨hda, hdb⟩ := hH_deriv_s_zero_at_ends s hs
    exact (hasDerivAt_homotopy_integral_zero
      f H a b s hab hH_smooth hf_holo hfH_cont
      hs hda hdb hf_differentiable).hasDerivWithinAt
  exact (constant_of_has_deriv_right_zero
    hI_cont hI_deriv_zero 1
    (by norm_num : (1 : ℝ) ∈ Icc 0 1)).symm

end
