/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.GeneralizedResidueTheory.Basic
import LeanPool.LeanModularForms.GeneralizedResidueTheory.OnCurvePV.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# Proposition 2.2: Finite Crossings and Isolated Crossing Intervals

For a `PiecewiseC1Immersion` γ : [a,b] → ℂ, we prove that the set of parameter
values where γ passes through a given point z₀ is finite. This is
Proposition 2.2 from Hungerbuhler-Wasem.

## Main Results

* `finite_crossings` — the set `{t ∈ Icc a b | γ t = z₀}` is finite
* `exists_isolated_crossing_interval` — each crossing has an isolating sub-interval

## Proof Strategy

At smooth points, `HasDerivAt.eventually_ne` (from `deriv_ne_zero`) shows crossings
are isolated. At partition points, one-sided derivative limits are nonzero, which
also gives isolation on each side via strict monotonicity of a real projection.
The crossing set is closed and has no accumulation points, hence finite by compactness.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ### Helper: HasDerivAt for real part composition -/

/-- If `f` has derivative `f'` at `x`, then `Re ∘ f` has derivative `Re(f')` at `x`. -/
private lemma HasDerivAt.re' {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun t => (f t).re) f'.re x :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt x h

/-! ### Eventually not in partition (shared pattern) -/

/-- The partition minus a point is finite hence closed; its complement is a nhds of `p`. -/
private lemma eventually_not_in_partition_left
    (γ : PiecewiseC1Immersion) (p : ℝ) :
    ∀ᶠ t in 𝓝[<] p, t ∉ γ.toPiecewiseC1Curve.partition := by
  have hcl : IsClosed ((↑γ.toPiecewiseC1Curve.partition \ {p} : Set ℝ)) :=
    (γ.toPiecewiseC1Curve.partition.finite_toSet.subset diff_subset).isClosed
  have hmem : p ∉ (↑γ.toPiecewiseC1Curve.partition \ {p} : Set ℝ) := by
    simp only [Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff, not_and, not_not,
      implies_true]
  have h1 : ∀ᶠ t in 𝓝[<] p, t ∈ (↑γ.toPiecewiseC1Curve.partition \ {p} : Set ℝ)ᶜ :=
    eventually_nhdsWithin_of_eventually_nhds (hcl.isOpen_compl.mem_nhds hmem)
  have h2 : ∀ᶠ t in 𝓝[<] p, t < p := eventually_nhdsWithin_of_forall fun t ht => ht
  exact (h1.and h2).mono fun t ⟨ht_compl, ht_lt⟩ ht_part =>
    ht_compl ⟨ht_part, ne_of_lt ht_lt⟩

private lemma eventually_not_in_partition_right
    (γ : PiecewiseC1Immersion) (p : ℝ) :
    ∀ᶠ t in 𝓝[>] p, t ∉ γ.toPiecewiseC1Curve.partition := by
  have hcl : IsClosed ((↑γ.toPiecewiseC1Curve.partition \ {p} : Set ℝ)) :=
    (γ.toPiecewiseC1Curve.partition.finite_toSet.subset diff_subset).isClosed
  have hmem : p ∉ (↑γ.toPiecewiseC1Curve.partition \ {p} : Set ℝ) := by
    simp only [Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff, not_and, not_not,
      implies_true]
  have h1 : ∀ᶠ t in 𝓝[>] p, t ∈ (↑γ.toPiecewiseC1Curve.partition \ {p} : Set ℝ)ᶜ :=
    eventually_nhdsWithin_of_eventually_nhds (hcl.isOpen_compl.mem_nhds hmem)
  have h2 : ∀ᶠ t in 𝓝[>] p, p < t := eventually_nhdsWithin_of_forall fun t ht => ht
  exact (h1.and h2).mono fun t ⟨ht_compl, ht_gt⟩ ht_part =>
    ht_compl ⟨ht_part, ne_of_gt ht_gt⟩

/-! ### Isolation of crossings at smooth points -/

/-- At a smooth point (not in partition) where γ(t₀) = z₀, there is a punctured
neighborhood in which γ(t) ≠ z₀. -/
theorem PiecewiseC1Immersion.eventually_ne_at_smooth_crossing
    (γ : PiecewiseC1Immersion) (z₀ : ℂ)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Icc γ.a γ.b)
    (hcross : γ.toFun t₀ = z₀)
    (hsmooth : t₀ ∉ γ.toPiecewiseC1Curve.partition) :
    ∀ᶠ t in 𝓝[≠] t₀, γ.toFun t ≠ z₀ := by
  exact hcross ▸ (γ.smooth_off_partition t₀ ht₀ hsmooth).hasDerivAt.eventually_ne
    (γ.deriv_ne_zero t₀ ht₀ hsmooth)

/-! ### Isolation of crossings at partition points -/

/-- At a partition point p with a < p, the left-sided derivative limit is nonzero,
so γ(t) ≠ γ(p) for t sufficiently close to p from the left. -/
theorem PiecewiseC1Immersion.eventually_ne_left_of_partition
    (γ : PiecewiseC1Immersion) (z₀ : ℂ)
    (p : ℝ) (hp : p ∈ γ.toPiecewiseC1Curve.partition)
    (hap : γ.a < p) (hpb : p ≤ γ.b)
    (hcross : γ.toFun p = z₀) :
    ∀ᶠ t in 𝓝[<] p, γ.toFun t ≠ z₀ := by
  obtain ⟨L, hL_ne, hL_tendsto⟩ := γ.left_deriv_limit p hp hap
  -- Define h(t) = Re(conj(L) * (γ(t) - z₀)).
  set h : ℝ → ℝ := fun t => ((starRingEnd ℂ L) * (γ.toFun t - z₀)).re with hh_def
  have hh_p : h p = 0 := by simp only [hh_def, hcross, sub_self, mul_zero, Complex.zero_re]
  -- (E1): Eventually t ∉ partition
  have h_ev_smooth : ∀ᶠ t in 𝓝[<] p, t ∉ γ.toPiecewiseC1Curve.partition :=
    eventually_not_in_partition_left γ p
  -- (E2): Eventually Re(conj(L) * γ'(t)) > 0
  have hL_sq_pos : (0 : ℝ) < ‖L‖ ^ 2 := by positivity
  have h_lim_val : (starRingEnd ℂ L * L).re = ‖L‖ ^ 2 := by
    have : starRingEnd ℂ L * L = (↑(‖L‖) : ℂ) ^ 2 := Complex.conj_mul' L
    rw [this, sq, ← Complex.ofReal_mul, Complex.ofReal_re, sq]
  have h_ev_deriv_pos : ∀ᶠ t in 𝓝[<] p,
      (starRingEnd ℂ L * deriv γ.toFun t).re > 0 := by
    have : Tendsto (fun t => (starRingEnd ℂ L * deriv γ.toFun t).re)
        (𝓝[<] p) (𝓝 (‖L‖ ^ 2)) := by
      rw [← h_lim_val]
      exact (continuous_re.tendsto _).comp
        (hL_tendsto.const_mul (starRingEnd ℂ L))
    exact this.eventually (Ioi_mem_nhds hL_sq_pos)
  -- (E3): Eventually t ∈ [a, b]
  have h_ev_Iab : ∀ᶠ t in 𝓝[<] p, t ∈ Icc γ.a γ.b := by
    have h1 : ∀ᶠ t in 𝓝[<] p, γ.a < t :=
      eventually_nhdsWithin_of_eventually_nhds (Ioi_mem_nhds hap)
    have h2 : ∀ᶠ t in 𝓝[<] p, t < p := eventually_nhdsWithin_of_forall fun t ht => ht
    exact (h1.and h2).mono fun t ⟨hat, htp⟩ => ⟨le_of_lt hat, le_trans (le_of_lt htp) hpb⟩
  -- Extract interval (q, p) where all hold
  have h_all : {t | t ∉ γ.toPiecewiseC1Curve.partition ∧
      (starRingEnd ℂ L * deriv γ.toFun t).re > 0 ∧ t ∈ Icc γ.a γ.b} ∈ 𝓝[<] p :=
    (h_ev_smooth.and (h_ev_deriv_pos.and h_ev_Iab))
  rw [mem_nhdsLT_iff_exists_Ioo_subset' hap] at h_all
  obtain ⟨q, hq_lt_p, hq_cond⟩ := h_all
  -- h is continuous on [q, p] ⊆ [a, b]
  have hqp_sub : Icc q p ⊆ Icc γ.a γ.b := by
    have h_ioo_sub : Ioo q p ⊆ Icc γ.a γ.b := fun t ht => (hq_cond ht).2.2
    have h_cl := closure_minimal h_ioo_sub isClosed_Icc
    rwa [closure_Ioo (ne_of_lt hq_lt_p)] at h_cl
  have hh_cont_qp : ContinuousOn h (Icc q p) :=
    (Complex.continuous_re.comp_continuousOn
      (continuousOn_const.mul (γ.continuous_toFun.mono hqp_sub |>.sub continuousOn_const)))
  -- h' > 0 on (q, p) = interior [q, p]
  have hh_deriv_pos : ∀ s ∈ interior (Icc q p), 0 < deriv h s := by
    rw [interior_Icc]
    intro s hs
    obtain ⟨hs_smooth, hs_deriv, hs_Iab⟩ := hq_cond hs
    -- Compute deriv h s = Re(conj(L) * γ'(s))
    have hh_has : HasDerivAt h ((starRingEnd ℂ L * deriv γ.toFun s).re) s :=
      (((γ.smooth_off_partition s hs_Iab hs_smooth).hasDerivAt.sub
        (hasDerivAt_const s z₀)).const_mul (starRingEnd ℂ L)).congr_deriv (by ring) |>.re'
    rw [hh_has.deriv]; exact hs_deriv
  -- h is strictly monotone on [q, p]; for t ∈ (q, p), h(t) < h(p) = 0
  have hh_mono := strictMonoOn_of_deriv_pos (convex_Icc q p) hh_cont_qp hh_deriv_pos
  rw [Filter.Eventually, mem_nhdsLT_iff_exists_Ioo_subset' hap]
  exact ⟨q, hq_lt_p, fun t ht hγt => by
    have hht : h t = 0 := by simp only [hh_def, hγt, sub_self, mul_zero, Complex.zero_re]
    have : h t < h p := hh_mono (Ioo_subset_Icc_self ht) (right_mem_Icc.mpr hq_lt_p.le) ht.2
    linarith⟩

/-- At a partition point p with p < b, the right-sided derivative limit is nonzero,
so γ(t) ≠ γ(p) for t sufficiently close to p from the right. -/
theorem PiecewiseC1Immersion.eventually_ne_right_of_partition
    (γ : PiecewiseC1Immersion) (z₀ : ℂ)
    (p : ℝ) (hp : p ∈ γ.toPiecewiseC1Curve.partition)
    (hap : γ.a ≤ p) (hpb : p < γ.b)
    (hcross : γ.toFun p = z₀) :
    ∀ᶠ t in 𝓝[>] p, γ.toFun t ≠ z₀ := by
  obtain ⟨L, hL_ne, hL_tendsto⟩ := γ.right_deriv_limit p hp hpb
  set h : ℝ → ℝ := fun t => ((starRingEnd ℂ L) * (γ.toFun t - z₀)).re with hh_def
  have hh_p : h p = 0 := by simp only [hh_def, hcross, sub_self, mul_zero, Complex.zero_re]
  -- (E1): Eventually t ∉ partition
  have h_ev_smooth : ∀ᶠ t in 𝓝[>] p, t ∉ γ.toPiecewiseC1Curve.partition :=
    eventually_not_in_partition_right γ p
  -- (E2): Eventually derivative positive
  have hL_sq_pos : (0 : ℝ) < ‖L‖ ^ 2 := by positivity
  have h_lim_val : (starRingEnd ℂ L * L).re = ‖L‖ ^ 2 := by
    have : starRingEnd ℂ L * L = (↑(‖L‖) : ℂ) ^ 2 := Complex.conj_mul' L
    rw [this, sq, ← Complex.ofReal_mul, Complex.ofReal_re, sq]
  have h_ev_deriv_pos : ∀ᶠ t in 𝓝[>] p,
      (starRingEnd ℂ L * deriv γ.toFun t).re > 0 := by
    have : Tendsto (fun t => (starRingEnd ℂ L * deriv γ.toFun t).re)
        (𝓝[>] p) (𝓝 (‖L‖ ^ 2)) := by
      rw [← h_lim_val]
      exact (continuous_re.tendsto _).comp (hL_tendsto.const_mul (starRingEnd ℂ L))
    exact this.eventually (Ioi_mem_nhds hL_sq_pos)
  -- (E3): Eventually t ∈ [a, b]
  have h_ev_Iab : ∀ᶠ t in 𝓝[>] p, t ∈ Icc γ.a γ.b := by
    have h1 : ∀ᶠ t in 𝓝[>] p, t < γ.b :=
      eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds hpb)
    have h2 : ∀ᶠ t in 𝓝[>] p, p < t := eventually_nhdsWithin_of_forall fun t ht => ht
    exact (h1.and h2).mono fun t ⟨htb, htp⟩ => ⟨le_trans hap (le_of_lt htp), le_of_lt htb⟩
  -- Extract interval (p, r)
  have h_all : {t | t ∉ γ.toPiecewiseC1Curve.partition ∧
      (starRingEnd ℂ L * deriv γ.toFun t).re > 0 ∧ t ∈ Icc γ.a γ.b} ∈ 𝓝[>] p :=
    h_ev_smooth.and (h_ev_deriv_pos.and h_ev_Iab)
  rw [mem_nhdsGT_iff_exists_Ioo_subset' hpb] at h_all
  obtain ⟨r, hr_gt_p, hr_cond⟩ := h_all
  -- h is continuous on [p, r] ⊆ [a, b]
  have hpr_sub : Icc p r ⊆ Icc γ.a γ.b := by
    have h_ioo_sub : Ioo p r ⊆ Icc γ.a γ.b := fun t ht => (hr_cond ht).2.2
    have h_cl := closure_minimal h_ioo_sub isClosed_Icc
    rwa [closure_Ioo (ne_of_lt hr_gt_p)] at h_cl
  have hh_cont_pr : ContinuousOn h (Icc p r) :=
    (Complex.continuous_re.comp_continuousOn
      (continuousOn_const.mul (γ.continuous_toFun.mono hpr_sub |>.sub continuousOn_const)))
  -- h' > 0 on (p, r)
  have hh_deriv_pos : ∀ s ∈ interior (Icc p r), 0 < deriv h s := by
    rw [interior_Icc]
    intro s hs
    obtain ⟨hs_smooth, hs_deriv, hs_Iab⟩ := hr_cond hs
    have hh_has : HasDerivAt h ((starRingEnd ℂ L * deriv γ.toFun s).re) s :=
      (((γ.smooth_off_partition s hs_Iab hs_smooth).hasDerivAt.sub
        (hasDerivAt_const s z₀)).const_mul (starRingEnd ℂ L)).congr_deriv (by ring) |>.re'
    rw [hh_has.deriv]; exact hs_deriv
  -- h is strictly monotone on [p, r]; for t ∈ (p, r), h(p) = 0 < h(t)
  have hh_mono := strictMonoOn_of_deriv_pos (convex_Icc p r) hh_cont_pr hh_deriv_pos
  rw [Filter.Eventually, mem_nhdsGT_iff_exists_Ioo_subset' hpb]
  exact ⟨r, hr_gt_p, fun t ht hγt => by
    have hht : h t = 0 := by simp only [hh_def, hγt, sub_self, mul_zero, Complex.zero_re]
    have : h p < h t := hh_mono (left_mem_Icc.mpr hr_gt_p.le) (Ioo_subset_Icc_self ht) ht.1
    linarith⟩

/-! ### Crossings are isolated -/

/-- At any crossing t₀ ∈ [a, b], there is a punctured neighborhood with no
other crossings in [a,b]. -/
theorem PiecewiseC1Immersion.crossing_isolated_nhds
    (γ : PiecewiseC1Immersion) (z₀ : ℂ)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Icc γ.a γ.b)
    (hcross : γ.toFun t₀ = z₀) :
    ∀ᶠ t in 𝓝[≠] t₀, γ.toFun t ≠ z₀ ∨ t ∉ Icc γ.a γ.b := by
  by_cases hpart : t₀ ∈ γ.toPiecewiseC1Curve.partition
  · rw [punctured_nhds_eq_nhdsWithin_sup_nhdsWithin, Filter.eventually_sup]
    constructor
    · by_cases hap : γ.a < t₀
      · exact (γ.eventually_ne_left_of_partition z₀ t₀ hpart hap ht₀.2 hcross).mono
          (fun t ht => Or.inl ht)
      · have hle : t₀ ≤ γ.a := not_lt.mp hap
        apply Filter.Eventually.mono
          (eventually_nhdsWithin_of_forall (fun t (ht : t < t₀) => ht))
        intro t ht; right
        simp only [mem_Icc, not_and_or, not_le]
        left; linarith
    · by_cases hpb : t₀ < γ.b
      · exact (γ.eventually_ne_right_of_partition z₀ t₀ hpart ht₀.1 hpb hcross).mono
          (fun t ht => Or.inl ht)
      · have hle : γ.b ≤ t₀ := not_lt.mp hpb
        apply Filter.Eventually.mono
          (eventually_nhdsWithin_of_forall (fun t (ht : t₀ < t) => ht))
        intro t ht; right
        simp only [mem_Icc, not_and_or, not_le]
        right; linarith
  · exact (γ.eventually_ne_at_smooth_crossing z₀ t₀ ht₀ hcross hpart).mono
      (fun t ht => Or.inl ht)

/-- No point of the crossing set is an accumulation point. -/
theorem PiecewiseC1Immersion.crossing_not_accPt
    (γ : PiecewiseC1Immersion) (z₀ : ℂ)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Icc γ.a γ.b)
    (hcross : γ.toFun t₀ = z₀) :
    ¬AccPt t₀ (𝓟 {t ∈ Icc γ.a γ.b | γ.toFun t = z₀}) := by
  rw [accPt_iff_frequently_nhdsNE, Filter.not_frequently]
  exact (γ.crossing_isolated_nhds z₀ t₀ ht₀ hcross).mono
    (fun t ht ht_mem => by
      simp only [mem_setOf_eq] at ht_mem
      exact ht.elim (fun h => h ht_mem.2) (fun h => h ht_mem.1))

/-- The crossing set is closed. -/
theorem crossing_set_isClosed (γ : PiecewiseC1Immersion) (z₀ : ℂ) :
    IsClosed {t ∈ Icc γ.a γ.b | γ.toFun t = z₀} := by
  have : {t ∈ Icc γ.a γ.b | γ.toFun t = z₀} = Icc γ.a γ.b ∩ γ.toFun ⁻¹' {z₀} := by
    ext t; simp only [Set.mem_sep_iff, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff]
  rw [this]
  exact γ.continuous_toFun.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton

/-! ### Main theorem -/

/-- **Proposition 2.2**: The crossing set is finite. -/
theorem finite_crossings (γ : PiecewiseC1Immersion) (z₀ : ℂ) :
    Set.Finite {t ∈ Icc γ.a γ.b | γ.toFun t = z₀} := by
  set S := {t ∈ Icc γ.a γ.b | γ.toFun t = z₀}
  by_contra hS_not_fin
  have hS_inf : S.Infinite := hS_not_fin
  obtain ⟨x, _, hx_acc⟩ :=
    hS_inf.exists_accPt_of_subset_isCompact isCompact_Icc (fun t (ht : t ∈ S) => ht.1)
  have hx_closure : x ∈ closure S := mem_closure_iff_clusterPt.mpr hx_acc.clusterPt
  have hx_S : x ∈ S := by rwa [(crossing_set_isClosed γ z₀).closure_eq] at hx_closure
  exact γ.crossing_not_accPt z₀ x hx_S.1 hx_S.2 hx_acc

/-! ### Isolated crossing intervals -/

/-- For each crossing, there exists an isolating sub-interval. -/
theorem exists_isolated_crossing_interval
    (γ : PiecewiseC1Immersion) (z₀ : ℂ)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b)
    (hcross : γ.toFun t₀ = z₀) :
    ∃ a' b' : ℝ, a' < t₀ ∧ t₀ < b' ∧
      Icc a' b' ⊆ Icc γ.a γ.b ∧
      (∀ t ∈ Icc a' b', γ.toFun t = z₀ → t = t₀) ∧
      (∀ t ∈ Ioo a' b', t ∉ γ.toPiecewiseC1Curve.partition →
        DifferentiableAt ℝ γ.toFun t) := by
  -- Get isolation from crossing_isolated_nhds: near t₀, γ(t) ≠ z₀ or t ∉ [a,b]
  have h_isol := γ.crossing_isolated_nhds z₀ t₀ (Ioo_subset_Icc_self ht₀) hcross
  -- Extract a neighborhood in 𝓝 t₀ from the punctured neighborhood
  rw [eventually_nhdsWithin_iff] at h_isol
  -- Get an open interval (l, u) around t₀ where the isolation holds
  obtain ⟨l, u, ⟨hl_lt, hlt_u⟩, h_Ioo⟩ := h_isol.exists_Ioo_subset
  -- Pick a' and b' strictly between l/a and t₀, t₀ and u/b respectively,
  -- ensuring Icc a' b' ⊆ Ioo l u (so h_Ioo applies to all points)
  -- and Icc a' b' ⊆ Icc a b (for membership).
  set a' := (max l γ.a + t₀) / 2 with ha'_def
  set b' := (t₀ + min u γ.b) / 2 with hb'_def
  have h_max_lt : max l γ.a < t₀ := max_lt hl_lt ht₀.1
  have h_t₀_lt_min : t₀ < min u γ.b := lt_min hlt_u ht₀.2
  have ha'_lt : a' < t₀ := by linarith
  have ht₀_lt_b' : t₀ < b' := by linarith
  have hl_lt_a' : l < a' := by
    have : l ≤ max l γ.a := le_max_left _ _
    linarith
  have hb'_lt_u : b' < u := by
    have : min u γ.b ≤ u := min_le_left _ _
    linarith
  have ha_le_a' : γ.a ≤ a' := by
    have : γ.a ≤ max l γ.a := le_max_right _ _
    linarith
  have hb'_le_b : b' ≤ γ.b := by
    have : min u γ.b ≤ γ.b := min_le_right _ _
    linarith
  refine ⟨a', b', ha'_lt, ht₀_lt_b', ?_, ?_, ?_⟩
  · -- Icc a' b' ⊆ Icc γ.a γ.b
    intro t ht
    exact ⟨le_trans ha_le_a' ht.1, le_trans ht.2 hb'_le_b⟩
  · -- Unique crossing: ∀ t ∈ Icc a' b', γ(t) = z₀ → t = t₀
    intro t ht hγt
    by_contra h_ne
    -- t ∈ Icc a' b' ⊆ Ioo l u since l < a' ≤ t ≤ b' < u
    have ht_Ioo_lu : t ∈ Ioo l u :=
      ⟨lt_of_lt_of_le hl_lt_a' ht.1, lt_of_le_of_lt ht.2 hb'_lt_u⟩
    -- By h_Ioo: t ≠ t₀ → γ(t) ≠ z₀ ∨ t ∉ [a,b]
    have := h_Ioo ht_Ioo_lu h_ne
    rcases this with h_ne_z₀ | h_not_Icc
    · exact h_ne_z₀ hγt
    · exact h_not_Icc ⟨le_trans ha_le_a' ht.1, le_trans ht.2 hb'_le_b⟩
  · -- Differentiability off partition
    intro t ht ht_part
    have ht_Icc : t ∈ Icc γ.a γ.b :=
      ⟨le_trans ha_le_a' (Ioo_subset_Icc_self ht).1,
       le_trans (Ioo_subset_Icc_self ht).2 hb'_le_b⟩
    exact γ.smooth_off_partition t ht_Icc ht_part

/-! ### CPV existence for (z - z₀)⁻¹ along piecewise C¹ immersions -/

/-- At any crossing point of a PiecewiseC1Immersion that has ContDiffAt ℝ 2,
the derivative is nonzero.

At smooth points (off partition), the immersion condition gives this directly.
At partition points, ContDiffAt ℝ 2 implies continuity of the derivative,
so the derivative must agree with the nonzero one-sided limits. -/
private lemma continuousAt_deriv_of_contDiffAt_two
    {f : ℝ → ℂ} {x : ℝ} (h : ContDiffAt ℝ 2 f x) :
    ContinuousAt (deriv f) x := by
  -- ContDiffAt ℝ 2 gives ContDiffOn ℝ 2 f U for some open U ∋ x
  have h1 : ContDiffAt ℝ 1 f x := h.of_le (by norm_num)
  obtain ⟨U, hU_nhd, hU_cd⟩ := h1.contDiffOn (le_refl _) (by
    simp only [WithTop.one_eq_coe, ENat.top_ne_one, WithTop.one_ne_top, imp_self])
  obtain ⟨V, hVU, hV_open, hxV⟩ := mem_nhds_iff.mp hU_nhd
  have hV_cd : ContDiffOn ℝ 1 f V := hU_cd.mono hVU
  have h_cont_on : ContinuousOn (deriv f) V :=
    hV_cd.continuousOn_deriv_of_isOpen hV_open (le_refl _)
  exact h_cont_on.continuousAt (hV_open.mem_nhds hxV)

theorem PiecewiseC1Immersion.deriv_ne_zero_of_C2
    (γ : PiecewiseC1Immersion) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo γ.a γ.b)
    (hγ_C2 : ContDiffAt ℝ 2 γ.toFun t₀) :
    deriv γ.toFun t₀ ≠ 0 := by
  by_cases hpart : t₀ ∈ γ.toPiecewiseC1Curve.partition
  · -- At a partition point with C² regularity, the derivative is continuous
    have h_cont_at : ContinuousAt (deriv γ.toFun) t₀ :=
      continuousAt_deriv_of_contDiffAt_two hγ_C2
    -- Use right derivative limit (t₀ < b since t₀ ∈ Ioo a b)
    obtain ⟨L, hL_ne, hL_tend⟩ := γ.right_deriv_limit t₀ hpart ht₀.2
    -- The continuous derivative must equal L
    have h_eq : deriv γ.toFun t₀ = L :=
      tendsto_nhds_unique (h_cont_at.mono_left nhdsWithin_le_nhds) hL_tend
    rw [h_eq]; exact hL_ne
  · exact γ.deriv_ne_zero t₀ (Ioo_subset_Icc_self ht₀) hpart

/-- CPV of `(z - z₀)⁻¹` exists on a sub-interval with a single crossing,
given C² regularity at the crossing point.

This combines `pv_limit_via_dyadic` with `cpv_exists_from_shifted_tendsto`
to prove CPV existence on a sub-interval containing exactly one crossing. -/
theorem cpv_exists_single_crossing
    (γ : PiecewiseC1Immersion) (z₀ : ℂ)
    (a' b' t₀ : ℝ)
    (hat₀ : t₀ ∈ Ioo a' b')
    (hcross : γ.toFun t₀ = z₀)
    (h_sub : Icc a' b' ⊆ Icc γ.a γ.b)
    (h_inj : ∀ t ∈ Icc a' b', γ.toFun t = z₀ → t = t₀)
    (hγ_C2 : ContDiffAt ℝ 2 γ.toFun t₀)
    (h_cont_deriv : ContinuousOn (deriv γ.toFun) (Icc a' b'))
    (hγ_meas : Measurable γ.toFun) :
    CauchyPrincipalValueExists' (fun z => (z - z₀)⁻¹) γ.toFun a' b' z₀ := by
  -- Get nonzero derivative at t₀
  have ht₀_Ioo_ab : t₀ ∈ Ioo γ.a γ.b :=
    ⟨lt_of_le_of_lt (h_sub (left_mem_Icc.mpr (le_of_lt (lt_trans hat₀.1 hat₀.2)))).1
       hat₀.1,
     lt_of_lt_of_le hat₀.2
       (h_sub (right_mem_Icc.mpr (le_of_lt (lt_trans hat₀.1 hat₀.2)))).2⟩
  have hL_ne : deriv γ.toFun t₀ ≠ 0 := γ.deriv_ne_zero_of_C2 t₀ ht₀_Ioo_ab hγ_C2
  -- Apply pv_limit_via_dyadic
  have hγ_cont : ContinuousOn γ.toFun (Icc a' b') := γ.continuous_toFun.mono h_sub
  have h_inj' : ∀ t ∈ Icc a' b', γ.toFun t = γ.toFun t₀ → t = t₀ := by
    intro t ht hγt; exact h_inj t ht (hγt.trans hcross)
  obtain ⟨limit, h_limit⟩ := pv_limit_via_dyadic hat₀ hL_ne hγ_C2
    rfl h_cont_deriv hγ_meas hγ_cont h_inj'
  exact ⟨limit, h_limit.congr (fun ε => intervalIntegral.integral_congr
    (fun t _ => by rw [hcross]))⟩

/-- The cutoff integrand for `(z - z₀)⁻¹` is interval-integrable along a
piecewise C¹ curve. The integrand is bounded: `(γ(t) - z₀)⁻¹` is bounded by
`1/ε` on the region `‖γ(t) - z₀‖ > ε`, and the derivative is locally bounded
by continuity. -/
theorem cpv_integrand_intervalIntegrable
    (γ : PiecewiseC1Immersion) (z₀ : ℂ)
    (c d : ℝ) (hcd : c ≤ d)
    (h_sub : Icc c d ⊆ Icc γ.a γ.b)
    (ε : ℝ) (hε : 0 < ε) :
    IntervalIntegrable
      (fun t => if ε < ‖γ.toFun t - z₀‖
        then (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t else 0)
      volume c d := by
  -- Step 1: Derivative bound on [γ.a, γ.b] (hence on [c, d]).
  obtain ⟨D, hD⟩ := piecewiseC1Immersion_deriv_bounded γ
  have hD_nn : 0 ≤ D := (norm_nonneg _).trans (hD γ.a (left_mem_Icc.mpr γ.hab.le))
  -- Step 2: Bound + continuity off partition →
  -- intervalIntegrable_of_piecewise_continuousOn_bounded.
  -- The integrand is bounded by ε⁻¹ * D everywhere.
  -- It is continuous on (Icc c d) \ (γ.partition ∪ {t | ‖γ t - z₀‖ = ε}).
  -- Since continuity off a finite set is needed, we use AEStronglyMeasurable + bound instead.
  -- Use the pattern from Basic.lean: IntegrableOn → IntervalIntegrable.
  set g : ℝ → ℂ := fun t => if ε < ‖γ.toFun t - z₀‖
      then (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t else 0 with hg_def
  -- Step 2a: Bound.
  have h_bound : ∀ t ∈ Icc c d, ‖g t‖ ≤ ε⁻¹ * D := by
    intro t ht; simp only [hg_def]
    split_ifs with h
    · rw [norm_mul, norm_inv]
      exact mul_le_mul (inv_anti₀ hε h.le) (hD t (h_sub ht))
        (norm_nonneg _) (inv_nonneg.mpr hε.le)
    · simp only [norm_zero]; exact mul_nonneg (inv_nonneg.mpr hε.le) hD_nn
  -- Step 2b: AEStronglyMeasurable via piecewise construction.
  -- The set S = {t | ε < ‖γ t - z₀‖} ∩ Icc c d is measurable (preimage of open set).
  have hγ_cont_cd : ContinuousOn γ.toFun (Icc c d) := γ.continuous_toFun.mono h_sub
  have hS_meas : MeasurableSet ({t | ε < ‖γ.toFun t - z₀‖} ∩ Icc c d) :=
    measurableSet_norm_gt_Icc ε (hγ_cont_cd.sub continuousOn_const)
  -- The function g = piecewise S (f ∘ γ · γ') 0, and both pieces are AEStronglyMeasurable.
  -- On S, f ∘ γ · γ' is continuous off the partition. Off S, it's 0.
  -- We show g is AEStronglyMeasurable on Icc c d by splitting.
  have h_meas : AEStronglyMeasurable g (volume.restrict (Icc c d)) := by
    -- g agrees a.e. with the piecewise function
    let S := {t | ε < ‖γ.toFun t - z₀‖} ∩ Icc c d
    have h_pw : AEStronglyMeasurable
        (S.piecewise (fun t => (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t) (fun _ => (0 : ℂ)))
        volume := by
      apply AEStronglyMeasurable.piecewise hS_meas
      · -- On S: (γ t - z₀)⁻¹ * deriv γ t is a.e. strongly measurable on S
        -- since it's continuous off the partition
        have h_cont_on_S : ContinuousOn (fun t => (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t)
            (S \ γ.partition) := by
          intro t ⟨⟨ht_far, ht_Icc⟩, ht_notP⟩
          have h_ne : γ.toFun t - z₀ ≠ 0 := by
            intro heq; simp only [Set.mem_setOf_eq, heq, norm_zero] at ht_far; linarith
          apply ContinuousWithinAt.mul
          · have hγ_sub : ContinuousWithinAt (fun t => γ.toFun t - z₀)
                (S \ γ.partition) t :=
              (hγ_cont_cd.continuousWithinAt ht_Icc).sub continuousWithinAt_const
                |>.mono (fun x hx => hx.1.2)
            exact hγ_sub.inv₀ h_ne
          · by_cases ht_Ioo : t ∈ Ioo γ.a γ.b
            · exact (γ.toPiecewiseC1Curve.deriv_continuous_off_partition
                  t ht_Ioo ht_notP).continuousWithinAt
            · have ht_ab := h_sub ht_Icc
              have : t = γ.a ∨ t = γ.b := by
                simp only [Set.mem_Ioo, not_and, not_lt] at ht_Ioo
                rcases ht_ab.1.lt_or_eq with h | h
                · right; exact le_antisymm ht_ab.2 (ht_Ioo h)
                · left; exact h.symm
              rcases this with rfl | rfl
              · exact absurd γ.toPiecewiseC1Curve.endpoints_in_partition.1 ht_notP
              · exact absurd γ.toPiecewiseC1Curve.endpoints_in_partition.2 ht_notP
        have h_diff_meas : MeasurableSet (S \ γ.partition) :=
          hS_meas.diff γ.partition.finite_toSet.measurableSet
        have h_P_null : volume (↑γ.partition ∩ S) = 0 :=
          (γ.partition.finite_toSet.inter_of_left S).measure_zero volume
        have h_P_inter_meas : MeasurableSet (↑γ.partition ∩ S) :=
          γ.partition.finite_toSet.measurableSet.inter hS_meas
        have h_eq_S : S = (S \ γ.partition) ∪ (↑γ.partition ∩ S) := by
          ext x; simp only [S, Set.mem_union, Set.mem_diff, Set.mem_inter_iff]; tauto
        have h_restrict_eq : volume.restrict S =
            volume.restrict ((S \ γ.partition) ∪ (↑γ.partition ∩ S)) := by
          rw [← h_eq_S]
        rw [h_restrict_eq, aestronglyMeasurable_union_iff]
        exact ⟨h_cont_on_S.aestronglyMeasurable h_diff_meas,
          (Measure.restrict_zero_set h_P_null).symm ▸ aestronglyMeasurable_zero_measure _⟩
      · exact aestronglyMeasurable_const
    have h_eq_ae : g =ᵐ[volume.restrict (Icc c d)]
        S.piecewise (fun t => (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t) (fun _ => 0) := by
      filter_upwards [ae_restrict_mem isClosed_Icc.measurableSet] with t ht
      simp only [hg_def, piecewise]
      split_ifs with h1 h2 h2
      · rfl
      · exfalso; exact h2 ⟨h1, ht⟩
      · exfalso; exact h1 h2.1
      · rfl
    exact (h_pw.mono_measure Measure.restrict_le_self).congr h_eq_ae.symm
  -- Step 3: Combine measurability + bound → IntegrableOn → IntervalIntegrable.
  have hf_int : IntegrableOn g (Icc c d) volume :=
    IntegrableOn.of_bound
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
      h_meas (ε⁻¹ * D)
      (by filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht; exact h_bound t ht)
  exact (uIcc_of_le hcd ▸ hf_int).intervalIntegrable

/-- Helper: CPV of `(z - z₀)⁻¹` exists on any sub-interval `[c, d] ⊆ [a, b]`
where there are no crossings. This follows directly from `cpv_avoidance`. -/
private theorem cpv_avoidance_sub
    (γ : PiecewiseC1Immersion) (z₀ : ℂ)
    (c d : ℝ) (hcd : c ≤ d) (h_sub : Icc c d ⊆ Icc γ.a γ.b)
    (h_avoid : ∀ t ∈ Icc c d, γ.toFun t ≠ z₀) :
    CauchyPrincipalValueExists' (fun z => (z - z₀)⁻¹) γ.toFun c d z₀ :=
  cpv_avoidance _ γ.toFun c d z₀ (γ.continuous_toFun.mono h_sub) hcd h_avoid

/-- CPV of `(z - z₀)⁻¹` exists on a sub-interval `[c, d] ⊆ [a, b]`, assuming:
- γ doesn't cross z₀ at c or d
- C² regularity and continuous derivative hold at each crossing in (c, d)
- The number of crossings in [c, d] is at most `n`

This is proved by induction on `n`. -/
private theorem cpv_exists_on_subinterval
    (γ : PiecewiseC1Immersion) (z₀ : ℂ)
    (hγ_meas : Measurable γ.toFun)
    (n : ℕ)
    (c d : ℝ) (hcd : c ≤ d) (h_sub : Icc c d ⊆ Icc γ.a γ.b)
    (h_no_endpt : γ.toFun c ≠ z₀ ∧ γ.toFun d ≠ z₀)
    (h_fin_cd : Set.Finite {t ∈ Icc c d | γ.toFun t = z₀})
    (h_card : h_fin_cd.toFinset.card ≤ n)
    (hC2 : ∀ t ∈ Ioo c d, γ.toFun t = z₀ → ContDiffAt ℝ 2 γ.toFun t)
    (h_cont_deriv_cross : ∀ t ∈ Ioo c d, γ.toFun t = z₀ →
      ∃ a' b', t ∈ Ioo a' b' ∧ Icc a' b' ⊆ Icc γ.a γ.b ∧
        ContinuousOn (deriv γ.toFun) (Icc a' b')) :
    CauchyPrincipalValueExists' (fun z => (z - z₀)⁻¹) γ.toFun c d z₀ := by
  induction n generalizing c d with
  | zero =>
    -- No crossings at all
    apply cpv_avoidance_sub γ z₀ c d hcd h_sub
    intro t ht hγt
    have hmem : t ∈ h_fin_cd.toFinset := h_fin_cd.mem_toFinset.mpr ⟨ht, hγt⟩
    exact absurd hmem (Finset.card_eq_zero.mp (Nat.le_zero.mp h_card) ▸ Finset.notMem_empty t)
  | succ n ih =>
    -- Check if there are any crossings
    by_cases h_empty : h_fin_cd.toFinset = ∅
    · apply cpv_avoidance_sub γ z₀ c d hcd h_sub
      intro t ht hγt
      exact absurd (h_fin_cd.mem_toFinset.mpr ⟨ht, hγt⟩) (h_empty ▸ Finset.notMem_empty t)
    · -- There exists at least one crossing in [c,d]
      obtain ⟨t₁, ht₁_mem⟩ := Finset.nonempty_of_ne_empty h_empty
      have ht₁_Icc : t₁ ∈ Icc c d := (h_fin_cd.mem_toFinset.mp ht₁_mem).1
      have hγt₁ : γ.toFun t₁ = z₀ := (h_fin_cd.mem_toFinset.mp ht₁_mem).2
      -- Since c and d are not crossings, t₁ must be in (c,d)
      have ht₁_Ioo : t₁ ∈ Ioo c d :=
        ⟨lt_of_le_of_ne ht₁_Icc.1 (fun h => h_no_endpt.1 (h ▸ hγt₁)),
         lt_of_le_of_ne ht₁_Icc.2 (fun h => h_no_endpt.2 (h ▸ hγt₁))⟩
      -- t₁ ∈ Ioo a b (since [c,d] ⊆ [a,b] and t₁ ∈ (c,d))
      have ht₁_Ioo_ab : t₁ ∈ Ioo γ.a γ.b :=
        ⟨lt_of_le_of_lt (h_sub (left_mem_Icc.mpr hcd)).1 ht₁_Ioo.1,
         lt_of_lt_of_le ht₁_Ioo.2 (h_sub (right_mem_Icc.mpr hcd)).2⟩
      -- Get isolating interval for t₁
      obtain ⟨a', b', ha'_lt, ht₁_lt_b', hab'_sub_ab, h_unique, _⟩ :=
        exists_isolated_crossing_interval γ z₀ t₁ ht₁_Ioo_ab hγt₁
      -- Get C² and continuous-deriv data
      have hC2_t₁ := hC2 t₁ ht₁_Ioo hγt₁
      obtain ⟨a₀, b₀, ht₁_Ioo_a₀b₀, _hab₀_sub, h_a₀b₀_cont⟩ :=
        h_cont_deriv_cross t₁ ht₁_Ioo hγt₁
      -- Intersect isolating interval with continuous-deriv interval and with (c,d)
      -- to get [α, β] with α < t₁ < β, [α,β] ⊆ [a',b'] ∩ [a₀,b₀] ∩ [c,d]
      set α := max (max a' a₀) c with hα_def
      set β := min (min b' b₀) d with hβ_def
      have hα_lt_t₁ : α < t₁ := by
        simp only [hα_def, max_lt_iff]
        exact ⟨⟨ha'_lt, ht₁_Ioo_a₀b₀.1⟩, ht₁_Ioo.1⟩
      have ht₁_lt_β : t₁ < β := by
        simp only [hβ_def, lt_min_iff]
        exact ⟨⟨ht₁_lt_b', ht₁_Ioo_a₀b₀.2⟩, ht₁_Ioo.2⟩
      -- [α, β] ⊆ [a', b'] (for uniqueness)
      have hαβ_sub_a'b' : Icc α β ⊆ Icc a' b' := fun t ht =>
        ⟨(le_max_left _ _).trans ((le_max_left _ _).trans ht.1),
         ht.2.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
      -- [α, β] ⊆ [a₀, b₀] (for continuous deriv)
      have hαβ_sub_a₀b₀ : Icc α β ⊆ Icc a₀ b₀ := fun t ht =>
        ⟨(le_max_right _ _).trans ((le_max_left _ _).trans ht.1),
         ht.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
      -- [α, β] ⊆ [c, d]
      have hαβ_sub_cd : Icc α β ⊆ Icc c d := fun t ht =>
        ⟨(le_max_right _ _).trans ht.1, ht.2.trans (min_le_right _ _)⟩
      -- [α, β] ⊆ [a, b]
      have hαβ_sub_ab : Icc α β ⊆ Icc γ.a γ.b := fun t ht => h_sub (hαβ_sub_cd ht)
      -- Uniqueness on [α, β]
      have h_unique_αβ : ∀ t ∈ Icc α β, γ.toFun t = z₀ → t = t₁ :=
        fun t ht hγt => h_unique t (hαβ_sub_a'b' ht) hγt
      -- Continuous derivative on [α, β]
      have h_cont_αβ : ContinuousOn (deriv γ.toFun) (Icc α β) :=
        h_a₀b₀_cont.mono hαβ_sub_a₀b₀
      -- γ(α) ≠ z₀ and γ(β) ≠ z₀
      have hαβ_lt : α < β := lt_trans hα_lt_t₁ ht₁_lt_β
      have hα_ne : γ.toFun α ≠ z₀ := fun h =>
        absurd (h_unique_αβ α (left_mem_Icc.mpr hαβ_lt.le) h) (ne_of_lt hα_lt_t₁)
      have hβ_ne : γ.toFun β ≠ z₀ := fun h =>
        absurd (h_unique_αβ β (right_mem_Icc.mpr hαβ_lt.le) h) (ne_of_gt ht₁_lt_β)
      -- CPV on [α, β] via cpv_exists_single_crossing
      have h_cpv_mid : CauchyPrincipalValueExists'
          (fun z => (z - z₀)⁻¹) γ.toFun α β z₀ :=
        cpv_exists_single_crossing γ z₀ α β t₁ ⟨hα_lt_t₁, ht₁_lt_β⟩
          hγt₁ hαβ_sub_ab h_unique_αβ hC2_t₁ h_cont_αβ hγ_meas
      -- [c, α] and [β, d] have strictly fewer crossings
      have hcα : c ≤ α := le_max_right _ _
      have hβd : β ≤ d := min_le_right _ _
      have hcα_sub : Icc c α ⊆ Icc γ.a γ.b :=
        fun t ht => h_sub ⟨ht.1, ht.2.trans (hαβ_sub_cd (left_mem_Icc.mpr hαβ_lt.le)).2⟩
      have hβd_sub : Icc β d ⊆ Icc γ.a γ.b :=
        fun t ht => h_sub ⟨(hαβ_sub_cd (right_mem_Icc.mpr hαβ_lt.le)).1.trans ht.1, ht.2⟩
      -- Crossings in [c, α]: subset of [c, d] crossings minus t₁
      -- (since t₁ > α, t₁ ∉ [c, α])
      have h_fin_cα : Set.Finite {t ∈ Icc c α | γ.toFun t = z₀} :=
        h_fin_cd.subset (fun t ⟨ht, hγt⟩ =>
          ⟨⟨ht.1, ht.2.trans
            (hαβ_sub_cd (left_mem_Icc.mpr hαβ_lt.le)).2⟩, hγt⟩)
      have h_fin_βd : Set.Finite {t ∈ Icc β d | γ.toFun t = z₀} :=
        h_fin_cd.subset (fun t ⟨ht, hγt⟩ =>
          ⟨⟨(hαβ_sub_cd (right_mem_Icc.mpr hαβ_lt.le)).1.trans
            ht.1, ht.2⟩, hγt⟩)
      -- t₁ is in the [c,d] crossing set but not in either sub-crossing set
      have ht₁_not_cα : t₁ ∉ {t ∈ Icc c α | γ.toFun t = z₀} :=
        fun ⟨ht, _⟩ => absurd ht.2 (not_le.mpr hα_lt_t₁)
      have ht₁_not_βd : t₁ ∉ {t ∈ Icc β d | γ.toFun t = z₀} :=
        fun ⟨ht, _⟩ => absurd ht.1 (not_le.mpr ht₁_lt_β)
      -- Card bound: crossing set of [c,α] is a proper subset of [c,d] crossings
      have h_card_cα : h_fin_cα.toFinset.card ≤ n := by
        have h_sub_finset : h_fin_cα.toFinset ⊆ h_fin_cd.toFinset.erase t₁ := by
          intro t ht_mem
          refine Finset.mem_erase.mpr ⟨?_, h_fin_cd.mem_toFinset.mpr
            ((fun ⟨ht_Icc, hγt⟩ => ⟨⟨ht_Icc.1, ht_Icc.2.trans
              (hαβ_sub_cd (left_mem_Icc.mpr hαβ_lt.le)).2⟩, hγt⟩)
              (h_fin_cα.mem_toFinset.mp ht_mem))⟩
          intro heq; subst heq
          exact ht₁_not_cα (h_fin_cα.mem_toFinset.mp ht_mem)
        have h_le := Finset.card_le_card h_sub_finset
        have h_erase_card : (h_fin_cd.toFinset.erase t₁).card < h_fin_cd.toFinset.card :=
          Finset.card_erase_lt_of_mem ht₁_mem
        omega
      have h_card_βd : h_fin_βd.toFinset.card ≤ n := by
        have h_sub_finset : h_fin_βd.toFinset ⊆ h_fin_cd.toFinset.erase t₁ := by
          intro t ht_mem
          refine Finset.mem_erase.mpr ⟨?_, h_fin_cd.mem_toFinset.mpr
            ((fun ⟨ht_Icc, hγt⟩ => ⟨⟨(hαβ_sub_cd
              (right_mem_Icc.mpr hαβ_lt.le)).1.trans ht_Icc.1,
              ht_Icc.2⟩, hγt⟩)
              (h_fin_βd.mem_toFinset.mp ht_mem))⟩
          intro heq; subst heq
          exact ht₁_not_βd (h_fin_βd.mem_toFinset.mp ht_mem)
        have h_le := Finset.card_le_card h_sub_finset
        have h_erase_card : (h_fin_cd.toFinset.erase t₁).card < h_fin_cd.toFinset.card :=
          Finset.card_erase_lt_of_mem ht₁_mem
        omega
      -- Ioo c α ⊆ Ioo c d and Ioo β d ⊆ Ioo c d
      have h_Ioo_cα_cd : Ioo c α ⊆ Ioo c d := fun t ht =>
        ⟨ht.1, lt_of_lt_of_le ht.2 (hαβ_sub_cd (left_mem_Icc.mpr hαβ_lt.le)).2⟩
      have h_Ioo_βd_cd : Ioo β d ⊆ Ioo c d := fun t ht =>
        ⟨lt_of_le_of_lt (hαβ_sub_cd (right_mem_Icc.mpr hαβ_lt.le)).1 ht.1, ht.2⟩
      -- CPV on [c, α] by induction
      have h_cpv_left : CauchyPrincipalValueExists'
          (fun z => (z - z₀)⁻¹) γ.toFun c α z₀ :=
        ih c α hcα hcα_sub ⟨h_no_endpt.1, hα_ne⟩ h_fin_cα h_card_cα
          (fun t ht hγt => hC2 t (h_Ioo_cα_cd ht) hγt)
          (fun t ht hγt => h_cont_deriv_cross t (h_Ioo_cα_cd ht) hγt)
      -- CPV on [β, d] by induction
      have h_cpv_right : CauchyPrincipalValueExists'
          (fun z => (z - z₀)⁻¹) γ.toFun β d z₀ :=
        ih β d hβd hβd_sub ⟨hβ_ne, h_no_endpt.2⟩ h_fin_βd h_card_βd
          (fun t ht hγt => hC2 t (h_Ioo_βd_cd ht) hγt)
          (fun t ht hγt => h_cont_deriv_cross t (h_Ioo_βd_cd ht) hγt)
      -- Glue: [c, α] + [α, β] → [c, β], then [c, β] + [β, d] → [c, d]
      have h_cpv_cβ : CauchyPrincipalValueExists'
          (fun z => (z - z₀)⁻¹) γ.toFun c β z₀ :=
        cpv_concat _ γ.toFun c α β z₀ h_cpv_left h_cpv_mid hcα hαβ_lt.le
          (fun ε hε => cpv_integrand_intervalIntegrable γ z₀ c β
            (hcα.trans hαβ_lt.le) (fun t ht => h_sub ⟨ht.1, ht.2.trans hβd⟩) ε hε)
      exact cpv_concat _ γ.toFun c β d z₀ h_cpv_cβ h_cpv_right (hcα.trans hαβ_lt.le) hβd
        (fun ε hε => cpv_integrand_intervalIntegrable γ z₀ c d hcd h_sub ε hε)

/-- CPV of `(z - z₀)⁻¹` exists along a piecewise C¹ immersion.

Hypotheses:
- `hγ_meas`: γ is (Borel) measurable (follows from global continuity)
- `h_no_endpt`: γ doesn't cross z₀ at the endpoints a, b
- `hC2`: γ is C² at each interior crossing point
- `h_cont_deriv_cross`: the derivative is continuous near each crossing

The proof uses `cpv_exists_on_subinterval` with the cardinality of the full
crossing set as the induction bound. -/
theorem cpv_exists_inv_sub
    (γ : PiecewiseC1Immersion) (z₀ : ℂ)
    (hγ_meas : Measurable γ.toFun)
    (h_no_endpt : γ.toFun γ.a ≠ z₀ ∧ γ.toFun γ.b ≠ z₀)
    (hC2 : ∀ t ∈ Ioo γ.a γ.b, γ.toFun t = z₀ → ContDiffAt ℝ 2 γ.toFun t)
    (h_cont_deriv_cross : ∀ t ∈ Ioo γ.a γ.b, γ.toFun t = z₀ →
      ∃ a' b', t ∈ Ioo a' b' ∧ Icc a' b' ⊆ Icc γ.a γ.b ∧
        ContinuousOn (deriv γ.toFun) (Icc a' b')) :
    CauchyPrincipalValueExists' (fun z => (z - z₀)⁻¹) γ.toFun γ.a γ.b z₀ := by
  have h_fin := finite_crossings γ z₀
  exact cpv_exists_on_subinterval γ z₀ hγ_meas h_fin.toFinset.card
    γ.a γ.b γ.hab.le (le_refl _) h_no_endpt h_fin le_rfl
    (fun t ht hγt => hC2 t ht hγt)
    (fun t ht hγt => h_cont_deriv_cross t ht hγt)

/-- CPV of `(z - z₀)⁻¹` exists along a piecewise C¹ immersion, for the
common case where the curve is globally C² and measurable.

This is a simplified version of the general theorem where C² regularity
holds everywhere (not just at crossings), which is the typical case for
smooth curves like the fundamental domain boundary. -/
theorem cpv_exists_inv_sub_of_C2
    (γ : PiecewiseC1Immersion) (z₀ : ℂ)
    (hγ_meas : Measurable γ.toFun)
    (h_no_endpt : γ.toFun γ.a ≠ z₀ ∧ γ.toFun γ.b ≠ z₀)
    (hC2 : ∀ t ∈ Icc γ.a γ.b, ContDiffAt ℝ 2 γ.toFun t)
    (h_cont_deriv : ContinuousOn (deriv γ.toFun) (Icc γ.a γ.b)) :
    CauchyPrincipalValueExists' (fun z => (z - z₀)⁻¹) γ.toFun γ.a γ.b z₀ :=
  cpv_exists_inv_sub γ z₀ hγ_meas h_no_endpt
    (fun t ht _ => hC2 t (Ioo_subset_Icc_self ht))
    (fun _ ht _ => ⟨γ.a, γ.b, ht, le_refl _, h_cont_deriv⟩)

end
