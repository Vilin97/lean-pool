/-
Copyright (c) 2026 Nicholas Bulka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Bulka
-/

import Mathlib.Analysis.Complex.JensenFormula
import LeanPool.LiCriterion.Hadamard.Basic

/-!
Zero counting bounds from Jensen's formula.

This module packages one very specific estimate we use repeatedly:
if `order f ≤ 1`, then the number of (distinct) zeros in a disk grows like `O(r^(1+ε))`.

We express “distinct zeros” using the `MeromorphicOn.divisor` support on a closed ball; for an
analytic function this support is exactly the set of zeros in the ball (no poles).
-/

open Complex Real Filter Topology MeasureTheory
open scoped BigOperators

namespace Hadamard

namespace ZeroCounting

open Metric MeromorphicOn

/-! ### From `order ≤ 1` to a crude `maxModulus` upper bound -/

private lemma mul_card_le_sum_of_forall_le {α : Type*} (s : Finset α) (a : ℝ) (f : α → ℝ)
    (h : ∀ x ∈ s, a ≤ f x) : a * (s.card : ℝ) ≤ ∑ x ∈ s, f x := by
  classical
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert x s hx ih =>
      have hx' : a ≤ f x := h x (by simp [hx])
      have hs' : ∀ y ∈ s, a ≤ f y := by
        intro y hy
        exact h y (by simp [hy])
      have ih' : a * (s.card : ℝ) ≤ ∑ y ∈ s, f y := ih hs'
      -- `card (insert x s) = card s + 1`, `sum (insert x s) = f x + sum s`
      have hcard : ((insert x s).card : ℝ) = (s.card : ℝ) + 1 := by
        have : (insert x s).card = s.card + 1 := Finset.card_insert_of_notMem hx
        exact_mod_cast this
      have hsum : (∑ y ∈ insert x s, f y) = f x + ∑ y ∈ s, f y := by
        simpa using (Finset.sum_insert (f := f) (s := s) (a := x) hx)
      -- Combine
      calc
        a * ((insert x s).card : ℝ)
            = a * ((s.card : ℝ) + 1) := by simp [hcard]
        _ = a * (s.card : ℝ) + a := by ring
        _ ≤ (∑ y ∈ s, f y) + f x := by
              exact add_le_add ih' hx'
        _ = f x + ∑ y ∈ s, f y := by ac_rfl
        _ = ∑ y ∈ insert x s, f y := by simp [hsum]

private noncomputable def orderAux (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  if r > 0 ∧ maxModulus f r > 1 then
    Real.log (Real.log (maxModulus f r)) / Real.log r
  else 0

private lemma isBoundedUnder_orderAux_of_hasFiniteOrder (f : ℂ → ℂ) (hf : hasFiniteOrder f) :
    IsBoundedUnder (· ≤ ·) atTop (orderAux f) := by
  classical
  obtain ⟨hf_diff, ρ₀, R₀, hf_bound⟩ := hf
  refine isBoundedUnder_of_eventually_le (u := orderAux f) (a := max ρ₀ 0) ?_
  refine (eventually_atTop.2 ⟨max R₀ 2, ?_⟩)
  intro r hr
  have hr_ge_R0 : R₀ ≤ r := le_trans (le_max_left _ _) hr
  have hr_ge2 : (2 : ℝ) ≤ r := le_trans (le_max_right _ _) hr
  have hr_pos : 0 < r := by linarith
  have hr_gt1 : 1 < r := by linarith
  have hlogr_pos : 0 < Real.log r := Real.log_pos hr_gt1
  by_cases hM : maxModulus f r > 1
  · have hM_le : maxModulus f r ≤ Real.exp (r ^ ρ₀) := by
      refine maxModulus_le_of_forall_norm_le f hf_diff.continuous (le_of_lt hr_pos) ?_
      intro z hz
      have hRz : R₀ ≤ ‖z‖ := by simpa [hz] using hr_ge_R0
      exact le_of_lt (by simpa [hz] using hf_bound z hRz)
    have hlogM_le : Real.log (maxModulus f r) ≤ r ^ ρ₀ := by
      have hM_pos : 0 < maxModulus f r := lt_trans (by linarith) hM
      have := Real.log_le_log hM_pos hM_le
      simpa [Real.log_exp] using this
    have hlogM_pos : 0 < Real.log (maxModulus f r) := Real.log_pos hM
    have hloglog_le :
        Real.log (Real.log (maxModulus f r)) ≤ Real.log (r ^ ρ₀) :=
      Real.log_le_log hlogM_pos hlogM_le
    have hratio_le : Real.log (Real.log (maxModulus f r)) / Real.log r ≤ ρ₀ := by
      have hlogrpow : Real.log (r ^ ρ₀) = ρ₀ * Real.log r := Real.log_rpow hr_pos ρ₀
      have : Real.log (Real.log (maxModulus f r)) ≤ ρ₀ * Real.log r :=
        le_trans hloglog_le (by rw [hlogrpow])
      exact (div_le_iff₀ hlogr_pos).2 this
    have hcond : r > 0 ∧ maxModulus f r > 1 := ⟨hr_pos, hM⟩
    have : orderAux f r ≤ ρ₀ := by simpa [orderAux, hcond] using hratio_le
    exact le_trans this (le_max_left _ _)
  · have hcond : ¬(r > 0 ∧ maxModulus f r > 1) := by
      intro hcond
      exact hM hcond.2
    simp [orderAux, hcond, le_max_right _ _]

theorem maxModulus_le_exp_rpow_of_order_le_one (f : ℂ → ℂ)
    (hf_finite : hasFiniteOrder f) (hf_order_le : order f ≤ 1) :
    ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, ∀ r : ℝ, R₀ ≤ r → maxModulus f r ≤ Real.exp (r ^ (1 + ε)) := by
  classical
  intro ε hε
  have hu_bdd : IsBoundedUnder (· ≤ ·) atTop (orderAux f) :=
    isBoundedUnder_orderAux_of_hasFiniteOrder f hf_finite
  have h_limsup_le : Filter.limsup (orderAux f) atTop ≤ (1 : ℝ) := hf_order_le
  have hu_event : ∀ᶠ r : ℝ in atTop, orderAux f r < (1 : ℝ) + ε :=
    eventually_lt_add_pos_of_limsup_le (by simpa using hu_bdd) h_limsup_le hε
  -- also ensure `2 ≤ r` so `log r > 0`
  have hge2 : ∀ᶠ r : ℝ in atTop, (2 : ℝ) ≤ r := Filter.eventually_ge_atTop 2
  rcases (Filter.eventually_atTop.1 (hu_event.and hge2)) with ⟨R₀, hR₀⟩
  refine ⟨R₀, ?_⟩
  intro r hr
  have hr' := hR₀ r hr
  have haux_lt : orderAux f r < (1 : ℝ) + ε := hr'.1
  have hr_ge2 : (2 : ℝ) ≤ r := hr'.2
  have hr_pos : 0 < r := by linarith
  by_cases hM : maxModulus f r > 1
  · have hr_gt1 : 1 < r := by linarith
    have hlogr_pos : 0 < Real.log r := Real.log_pos hr_gt1
    have hcond : r > 0 ∧ maxModulus f r > 1 := ⟨hr_pos, hM⟩
    have hmain :
        Real.log (Real.log (maxModulus f r)) / Real.log r < (1 : ℝ) + ε := by
      simpa [orderAux, hcond] using haux_lt
    have hloglog :
        Real.log (Real.log (maxModulus f r)) < ((1 : ℝ) + ε) * Real.log r :=
      (div_lt_iff₀ hlogr_pos).1 hmain
    have hlogM_pos : 0 < Real.log (maxModulus f r) := Real.log_pos hM
    have hlogM : Real.log (maxModulus f r) < Real.exp (((1 : ℝ) + ε) * Real.log r) := by
      have hexp :
          Real.exp (Real.log (Real.log (maxModulus f r))) < Real.exp (((1 : ℝ) + ε) * Real.log r) :=
        (Real.exp_lt_exp).2 hloglog
      simpa [Real.exp_log hlogM_pos] using hexp
    have hexp_eq : Real.exp (((1 : ℝ) + ε) * Real.log r) = r ^ ((1 : ℝ) + ε) := by
      calc
        Real.exp (((1 : ℝ) + ε) * Real.log r) = Real.exp (Real.log r * ((1 : ℝ) + ε)) := by ring_nf
        _ = Real.exp (Real.log r) ^ ((1 : ℝ) + ε) := by simp [Real.exp_mul]
        _ = r ^ ((1 : ℝ) + ε) := by simp [Real.exp_log hr_pos]
    have hlogM' : Real.log (maxModulus f r) < r ^ ((1 : ℝ) + ε) := by
      simpa [hexp_eq] using hlogM
    have hM_pos : 0 < maxModulus f r := lt_trans (by linarith) hM
    have hM_lt : maxModulus f r < Real.exp (r ^ ((1 : ℝ) + ε)) := by
      have hexp : Real.exp (Real.log (maxModulus f r)) < Real.exp (r ^ ((1 : ℝ) + ε)) :=
        (Real.exp_lt_exp).2 hlogM'
      simpa [Real.exp_log hM_pos] using hexp
    exact le_of_lt hM_lt
  · -- If `M ≤ 1`, the bound is trivial since `exp(r^(1+ε)) ≥ 1`.
    have hM_le : maxModulus f r ≤ 1 := le_of_not_gt hM
    have hexp_ge : (1 : ℝ) ≤ Real.exp (r ^ ((1 : ℝ) + ε)) := by
      have : 0 ≤ r ^ ((1 : ℝ) + ε) := by
        exact Real.rpow_nonneg (le_of_lt hr_pos) _
      simpa using (Real.one_le_exp this)
    exact le_trans hM_le hexp_ge

/-- **General-order max-modulus growth bound.**

If `f` has finite order with `order f ≤ lam`, then for every `ε > 0` there is
`R₀` such that for all `r ≥ R₀`, `maxModulus f r ≤ Real.exp (r ^ (lam + ε))`.

This is the `order ≤ lam` analogue of
`maxModulus_le_exp_rpow_of_order_le_one`. The proof is exactly the same: the
specific constant `1` in the latter never interacts with the analysis, it is
simply the bound on the limsup. -/
theorem maxModulus_le_exp_rpow_of_order_le (f : ℂ → ℂ)
    (hf_finite : hasFiniteOrder f) {lam : ℝ} (hf_order_le : order f ≤ lam) :
    ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, ∀ r : ℝ, R₀ ≤ r →
      maxModulus f r ≤ Real.exp (r ^ (lam + ε)) := by
  classical
  intro ε hε
  have hu_bdd : IsBoundedUnder (· ≤ ·) atTop (orderAux f) :=
    isBoundedUnder_orderAux_of_hasFiniteOrder f hf_finite
  have h_limsup_le : Filter.limsup (orderAux f) atTop ≤ lam := hf_order_le
  have hu_event : ∀ᶠ r : ℝ in atTop, orderAux f r < lam + ε :=
    eventually_lt_add_pos_of_limsup_le (by simpa using hu_bdd) h_limsup_le hε
  have hge2 : ∀ᶠ r : ℝ in atTop, (2 : ℝ) ≤ r := Filter.eventually_ge_atTop 2
  rcases (Filter.eventually_atTop.1 (hu_event.and hge2)) with ⟨R₀, hR₀⟩
  refine ⟨R₀, ?_⟩
  intro r hr
  have hr' := hR₀ r hr
  have haux_lt : orderAux f r < lam + ε := hr'.1
  have hr_ge2 : (2 : ℝ) ≤ r := hr'.2
  have hr_pos : 0 < r := by linarith
  by_cases hM : maxModulus f r > 1
  · have hr_gt1 : 1 < r := by linarith
    have hlogr_pos : 0 < Real.log r := Real.log_pos hr_gt1
    have hcond : r > 0 ∧ maxModulus f r > 1 := ⟨hr_pos, hM⟩
    have hmain :
        Real.log (Real.log (maxModulus f r)) / Real.log r < lam + ε := by
      simpa [orderAux, hcond] using haux_lt
    have hloglog :
        Real.log (Real.log (maxModulus f r)) < (lam + ε) * Real.log r :=
      (div_lt_iff₀ hlogr_pos).1 hmain
    have hlogM_pos : 0 < Real.log (maxModulus f r) := Real.log_pos hM
    have hlogM : Real.log (maxModulus f r) < Real.exp ((lam + ε) * Real.log r) := by
      have hexp :
          Real.exp (Real.log (Real.log (maxModulus f r))) < Real.exp ((lam + ε) * Real.log r) :=
        (Real.exp_lt_exp).2 hloglog
      simpa [Real.exp_log hlogM_pos] using hexp
    have hexp_eq : Real.exp ((lam + ε) * Real.log r) = r ^ (lam + ε) := by
      calc
        Real.exp ((lam + ε) * Real.log r) = Real.exp (Real.log r * (lam + ε)) := by ring_nf
        _ = Real.exp (Real.log r) ^ (lam + ε) := by simp [Real.exp_mul]
        _ = r ^ (lam + ε) := by simp [Real.exp_log hr_pos]
    have hlogM' : Real.log (maxModulus f r) < r ^ (lam + ε) := by
      simpa [hexp_eq] using hlogM
    have hM_pos : 0 < maxModulus f r := lt_trans (by linarith) hM
    have hM_lt : maxModulus f r < Real.exp (r ^ (lam + ε)) := by
      have hexp : Real.exp (Real.log (maxModulus f r)) < Real.exp (r ^ (lam + ε)) :=
        (Real.exp_lt_exp).2 hlogM'
      simpa [Real.exp_log hM_pos] using hexp
    exact le_of_lt hM_lt
  · have hM_le : maxModulus f r ≤ 1 := le_of_not_gt hM
    have hexp_ge : (1 : ℝ) ≤ Real.exp (r ^ (lam + ε)) := by
      have : 0 ≤ r ^ (lam + ε) := by
        exact Real.rpow_nonneg (le_of_lt hr_pos) _
      simpa using (Real.one_le_exp this)
    exact le_trans hM_le hexp_ge

/-! ### Jensen ⇒ a bound on the number of zeros -/

theorem card_zeros_le_of_maxModulus (f : ℂ → ℂ) {R : ℝ} (hR : 0 < R)
    (hf_entire : Differentiable ℂ f) (hf0 : f 0 ≠ 0) (hM : (1 : ℝ) ≤ maxModulus f R) :
    (({u : ℂ |
          u ∈ (MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|)).support ∧ ‖u‖ ≤ R / 2} :
        Set ℂ).ncard : ℝ)
      ≤ (Real.log (maxModulus f R) - Real.log ‖f 0‖) / Real.log 2 := by
  classical
  -- Setup Jensen on `closedBall 0 R`.
  have hmer : MeromorphicOn f (closedBall (0 : ℂ) |R|) := fun z _ =>
    (hf_entire.analyticAt z).meromorphicAt
  have hCB0 : (0 : ℂ) ∈ closedBall (0 : ℂ) |R| := by
    simp [Metric.mem_closedBall, abs_nonneg R]
  have htrailing : meromorphicTrailingCoeffAt f 0 = f 0 := by
    simpa using (hf_entire.analyticAt 0).meromorphicTrailingCoeffAt_of_ne_zero hf0
  have hdiv0 : MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|) 0 = 0 := by
    -- `divisor` at `0` is `order.untop₀`, and the order is zero since `f 0 ≠ 0`.
    have horder0 : analyticOrderAt f 0 = 0 :=
      (hf_entire.analyticAt 0).analyticOrderAt_eq_zero.2 hf0
    have hmerOrder0 :
        meromorphicOrderAt f 0 = 0 := by
      simpa [horder0] using (hf_entire.analyticAt 0).meromorphicOrderAt_eq
    simp [MeromorphicOn.divisor_apply hmer hCB0, hmerOrder0]
  -- Jensen formula at the origin.
  have hjensen :
      Real.circleAverage (Real.log ‖f ·‖) 0 R
        = (∑ᶠ u, MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|) u * Real.log (R * ‖u‖⁻¹))
          + Real.log ‖f 0‖ := by
    have :=
      MeromorphicOn.circleAverage_log_norm (c := (0 : ℂ)) (R := R) (f := f)
        (by exact hR.ne') hmer
    -- simplify `‖0 - u‖ = ‖u‖`, divisor at 0, and trailing coefficient
    simpa [hdiv0, htrailing, norm_sub_rev, add_assoc, add_left_comm, add_comm, sub_eq_add_neg]
      using this
  -- Upper-bound the circle average by `log (maxModulus f R)` (pointwise, using `M ≥ 1`).
  have hCircleInt : CircleIntegrable (Real.log ‖f ·‖) 0 R := by
    apply MeromorphicOn.circleIntegrable_log_norm
    intro z hz
    have hz' : z ∈ closedBall (0 : ℂ) |R| := Metric.sphere_subset_closedBall hz
    exact hmer z hz'
  have havg_le :
      Real.circleAverage (Real.log ‖f ·‖) 0 R ≤ Real.log (maxModulus f R) := by
    refine
      Real.circleAverage_mono_on_of_le_circle (c := (0 : ℂ)) (R := R)
        (f := fun z => Real.log ‖f z‖) (a := Real.log (maxModulus f R)) hCircleInt ?_
    intro z hz
    have hzR : ‖z‖ = R := by simpa [Metric.mem_sphere, dist_eq_norm, abs_of_pos hR] using hz
    have hnorm : ‖f z‖ ≤ maxModulus f R := norm_le_maxModulus_on_circle f hf_entire.continuous hzR
    by_cases hfz : f z = 0
    · have hlogM_nonneg : 0 ≤ Real.log (maxModulus f R) := Real.log_nonneg hM
      simpa [hfz] using hlogM_nonneg
    · have hpos : 0 < ‖f z‖ := norm_pos_iff.2 hfz
      exact Real.log_le_log hpos hnorm
  -- Convert Jensen + `havg_le` into an upper bound on the finsum.
  have hsum_le :
      (∑ᶠ u, MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|) u * Real.log (R * ‖u‖⁻¹))
        ≤ Real.log (maxModulus f R) - Real.log ‖f 0‖ := by
    have := sub_le_sub_right havg_le (Real.log ‖f 0‖)
    -- `circleAverage = sum + log‖f0‖`
    -- so `sum = circleAverage - log‖f0‖`.
    simpa [hjensen, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
  -- Lower-bound the same finsum by `log 2 * (number of zeros with ‖u‖ ≤ R/2)`.
  let D : Function.locallyFinsuppWithin (closedBall (0 : ℂ) |R|) ℤ :=
    MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|)
  have hD_fin : (D.support : Set ℂ).Finite :=
    D.finiteSupport (isCompact_closedBall (0 : ℂ) |R|)
  have hD_nonneg : 0 ≤ D := by
    -- analytic ⇒ nonnegative divisor on the closed ball
    have hf_an : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) |R|) := by
      intro z _
      exact hf_entire.analyticAt z
    exact hf_an.divisor_nonneg
  let S : Set ℂ := {u : ℂ | u ∈ D.support ∧ ‖u‖ ≤ R / 2}
  have hS_fin : S.Finite := by
    refine hD_fin.subset ?_
    intro u hu
    exact hu.1
  have hlog2_pos : 0 < Real.log 2 := by
    simpa using (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  have hsum_ge :
      (Real.log 2) * (hS_fin.toFinset.card : ℝ)
        ≤ (∑ᶠ u, D u * Real.log (R * ‖u‖⁻¹)) := by
    -- Expand the finsum as a finite sum over the support.
    have hsupp :
        (Function.support fun u => (D u : ℝ) * Real.log (R * ‖u‖⁻¹)) ⊆ hD_fin.toFinset := by
      intro u hu
      -- if the term is nonzero, then `D u ≠ 0`, hence `u ∈ D.support`
      have ht_ne : (D u : ℝ) * Real.log (R * ‖u‖⁻¹) ≠ 0 := (Function.mem_support.1 hu)
      have hDu : D u ≠ 0 := by
        intro hDu0
        apply ht_ne
        simp [hDu0]
      have huD : u ∈ D.support := by
        have : u ∈ Function.support (fun x : ℂ => D x) := (Function.mem_support.2 hDu)
        simpa [Function.locallyFinsuppWithin.support] using this
      exact hD_fin.mem_toFinset.2 huD
    -- Restrict the sum to the support finset.
    have hsum_eq :
        (∑ᶠ u, D u * Real.log (R * ‖u‖⁻¹))
          = ∑ u ∈ hD_fin.toFinset, (D u : ℝ) * Real.log (R * ‖u‖⁻¹) := by
      simpa using
        (finsum_eq_sum_of_support_subset
          (f := fun u : ℂ => (D u : ℝ) * Real.log (R * ‖u‖⁻¹)) (s := hD_fin.toFinset) hsupp)
    -- Show each `u ∈ S` contributes at least `log 2`, and other terms are nonnegative.
    have hterm_ge : ∀ u ∈ hS_fin.toFinset, (Real.log 2 : ℝ) ≤ (D u : ℝ) * Real.log (R * ‖u‖⁻¹) := by
      intro u hu
      have huS : u ∈ S := (hS_fin.mem_toFinset).1 hu
      have hDu_ne : D u ≠ 0 := by
        have huD : u ∈ D.support := huS.1
        have huD' : u ∈ Function.support (fun x : ℂ => D x) := by
          simpa [Function.locallyFinsuppWithin.support] using huD
        exact (Function.mem_support.1 huD')
      have hDu_pos : (1 : ℤ) ≤ D u := by
        have hDu0 : (0 : ℤ) ≤ D u := hD_nonneg u
        have hlt : (0 : ℤ) < D u := lt_of_le_of_ne hDu0 (Ne.symm hDu_ne)
        -- `0 + 1 ≤ D u` ↔ `0 < D u`
        simpa [zero_add] using (Int.add_one_le_iff.2 hlt)
      have hu_ne0 : u ≠ 0 := by
        intro hu0
        -- would force `D 0 = 0` since `f 0 ≠ 0`
        have : D 0 = 0 := by simpa [D] using hdiv0
        have : D u = 0 := by simpa [hu0] using this
        exact hDu_ne this
      have hu_le : ‖u‖ ≤ R / 2 := huS.2
      have hu_pos : 0 < ‖u‖ := norm_pos_iff.2 hu_ne0
      have htwo : (2 : ℝ) ≤ R * ‖u‖⁻¹ := by
        have hmul : (2 : ℝ) * ‖u‖ ≤ R := by nlinarith
        have : (2 : ℝ) ≤ R / ‖u‖ := (le_div_iff₀ hu_pos).2 hmul
        simpa [div_eq_mul_inv] using this
      have hlog_ge : Real.log 2 ≤ Real.log (R * ‖u‖⁻¹) :=
        Real.log_le_log (by positivity : (0 : ℝ) < 2) htwo
      have hlog_nonneg : 0 ≤ Real.log (R * ‖u‖⁻¹) := by
        have h1 : (1 : ℝ) ≤ R * ‖u‖⁻¹ := le_trans (by norm_num : (1 : ℝ) ≤ 2) htwo
        exact Real.log_nonneg h1
      -- combine: `(D u : ℝ) ≥ 1` and `log(R/‖u‖) ≥ log 2`
      have hDu_ge1 : (1 : ℝ) ≤ (D u : ℝ) := by exact_mod_cast hDu_pos
      have hlog_ge' : (Real.log 2 : ℝ) ≤ (1 : ℝ) * Real.log (R * ‖u‖⁻¹) := by
        simpa [one_mul] using hlog_ge
      have := le_trans hlog_ge' (mul_le_mul_of_nonneg_right hDu_ge1 hlog_nonneg)
      simpa [one_mul, mul_assoc] using this
    -- The sum over the whole support dominates `log2 * card S`.
    have hcard_mul :
        (Real.log 2) * (hS_fin.toFinset.card : ℝ)
          ≤ ∑ u ∈ hS_fin.toFinset, (D u : ℝ) * Real.log (R * ‖u‖⁻¹) := by
      -- each summand ≥ log2
      have h := mul_card_le_sum_of_forall_le (s := hS_fin.toFinset) (a := Real.log 2)
        (f := fun u => (D u : ℝ) * Real.log (R * ‖u‖⁻¹)) hterm_ge
      simpa [mul_comm] using h
    -- enlarge from `S` to the full support by monotonicity (all terms are nonnegative)
    have hnonneg : ∀ u ∈ hD_fin.toFinset, 0 ≤ (D u : ℝ) * Real.log (R * ‖u‖⁻¹) := by
      intro u hu
      have hDu0 : (0 : ℤ) ≤ D u := hD_nonneg u
      have hDu0' : (0 : ℝ) ≤ (D u : ℝ) := by exact_mod_cast hDu0
      have hlog0 : 0 ≤ Real.log (R * ‖u‖⁻¹) := by
        -- `u` is in the support of `D`, hence `u ∈ closedBall 0 R`, so `‖u‖ ≤ R`
        have huU : u ∈ closedBall (0 : ℂ) |R| := by
          have : u ∈ D.support := hD_fin.mem_toFinset.1 hu
          exact D.supportWithinDomain this
        have hu_le : ‖u‖ ≤ |R| := by simpa [Metric.mem_closedBall, dist_eq_norm] using huU
        by_cases hu0 : u = 0
        · subst hu0
          simp
        · have hu_pos : 0 < ‖u‖ := norm_pos_iff.2 hu0
          have hmul_ge : (1 : ℝ) ≤ R * ‖u‖⁻¹ := by
            have : (1 : ℝ) ≤ R / ‖u‖ := by
              have hu_le' : ‖u‖ ≤ R := by simpa [abs_of_pos hR] using hu_le
              have : (1 : ℝ) * ‖u‖ ≤ R := by simpa [one_mul] using hu_le'
              exact (le_div_iff₀ hu_pos).2 this
            simpa [div_eq_mul_inv] using this
          exact Real.log_nonneg hmul_ge
      exact mul_nonneg hDu0' hlog0
    have hsub : hS_fin.toFinset ⊆ hD_fin.toFinset := by
      intro u hu
      have : u ∈ S := by simpa [hS_fin.mem_toFinset] using hu
      exact hD_fin.mem_toFinset.2 this.1
    have hsum_le' :
        (∑ u ∈ hS_fin.toFinset, (D u : ℝ) * Real.log (R * ‖u‖⁻¹))
          ≤ ∑ u ∈ hD_fin.toFinset, (D u : ℝ) * Real.log (R * ‖u‖⁻¹) := by
      have hnonneg' :
          ∀ u ∈ hD_fin.toFinset, u ∉ hS_fin.toFinset → 0 ≤ (D u : ℝ) * Real.log (R * ‖u‖⁻¹) := by
        intro u hu _
        exact hnonneg u hu
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg'
    -- combine everything and rewrite `finsum`
    have : (Real.log 2) * (hS_fin.toFinset.card : ℝ)
        ≤ ∑ u ∈ hD_fin.toFinset, (D u : ℝ) * Real.log (R * ‖u‖⁻¹) :=
      le_trans hcard_mul hsum_le'
    simpa [hsum_eq] using this
  -- Now finish by dividing by `log 2`.
  have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt hlog2_pos
  have hcard :
      (hS_fin.toFinset.card : ℝ) ≤ (Real.log (maxModulus f R) - Real.log ‖f 0‖) / Real.log 2 := by
    have h1 : (Real.log 2) * (hS_fin.toFinset.card : ℝ)
        ≤ Real.log (maxModulus f R) - Real.log ‖f 0‖ :=
      le_trans hsum_ge hsum_le
    -- divide by the positive constant `log 2`
    have := mul_le_mul_of_nonneg_left h1 (le_of_lt (inv_pos.2 hlog2_pos))
    -- rewrite `inv * (log2 * card) = card`
    -- and `inv * (rhs) = rhs / log2`
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hlog2_ne] using this
  have hcard' : ((S.ncard : ℝ)) ≤ (Real.log (maxModulus f R) - Real.log ‖f 0‖) / Real.log 2 := by
    simpa [Set.ncard_eq_toFinset_card S hS_fin] using hcard
  simpa [S] using hcard'

/-! ### Variant: avoid the `1 ≤ maxModulus f R` side condition

The lemma `card_zeros_le_of_maxModulus` assumes `1 ≤ maxModulus f R` in order to compare the
circle-average of `log ‖f‖` with `log (maxModulus f R)` even at points where `f` vanishes on the
circle (since `Real.log 0 = 0`).

For growth applications we want an unconditional bound, so we instead compare with
`log (max 1 (maxModulus f R))`.
-/

theorem card_zeros_le_of_max_one_maxModulus (f : ℂ → ℂ) {R : ℝ} (hR : 0 < R)
    (hf_entire : Differentiable ℂ f) (hf0 : f 0 ≠ 0) :
    (({u : ℂ |
          u ∈ (MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|)).support ∧ ‖u‖ ≤ R / 2} :
        Set ℂ).ncard : ℝ)
      ≤ (Real.log (max 1 (maxModulus f R)) - Real.log ‖f 0‖) / Real.log 2 := by
  classical
  -- Setup Jensen on `closedBall 0 R`.
  have hmer : MeromorphicOn f (closedBall (0 : ℂ) |R|) := fun z _ =>
    (hf_entire.analyticAt z).meromorphicAt
  have hCB0 : (0 : ℂ) ∈ closedBall (0 : ℂ) |R| := by
    simp [Metric.mem_closedBall, abs_nonneg R]
  have htrailing : meromorphicTrailingCoeffAt f 0 = f 0 := by
    simpa using (hf_entire.analyticAt 0).meromorphicTrailingCoeffAt_of_ne_zero hf0
  have hdiv0 : MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|) 0 = 0 := by
    have horder0 : analyticOrderAt f 0 = 0 :=
      (hf_entire.analyticAt 0).analyticOrderAt_eq_zero.2 hf0
    have hmerOrder0 : meromorphicOrderAt f 0 = 0 := by
      simpa [horder0] using (hf_entire.analyticAt 0).meromorphicOrderAt_eq
    simp [MeromorphicOn.divisor_apply hmer hCB0, hmerOrder0]
  -- Jensen formula at the origin.
  have hjensen :
      Real.circleAverage (Real.log ‖f ·‖) 0 R
        = (∑ᶠ u, MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|) u * Real.log (R * ‖u‖⁻¹))
          + Real.log ‖f 0‖ := by
    have :=
      MeromorphicOn.circleAverage_log_norm (c := (0 : ℂ)) (R := R) (f := f) (by exact hR.ne') hmer
    simpa [hdiv0, htrailing, norm_sub_rev, add_assoc, add_left_comm, add_comm, sub_eq_add_neg]
      using this
  -- Upper-bound the circle average by `log (max 1 (maxModulus f R))`.
  have hCircleInt : CircleIntegrable (Real.log ‖f ·‖) 0 R := by
    apply MeromorphicOn.circleIntegrable_log_norm
    intro z hz
    have hz' : z ∈ closedBall (0 : ℂ) |R| := Metric.sphere_subset_closedBall hz
    exact hmer z hz'
  have havg_le :
      Real.circleAverage (Real.log ‖f ·‖) 0 R ≤ Real.log (max 1 (maxModulus f R)) := by
    refine
      Real.circleAverage_mono_on_of_le_circle (c := (0 : ℂ)) (R := R)
        (f := fun z => Real.log ‖f z‖) (a := Real.log (max 1 (maxModulus f R))) hCircleInt ?_
    intro z hz
    have hzR : ‖z‖ = R := by simpa [Metric.mem_sphere, dist_eq_norm, abs_of_pos hR] using hz
    have hnorm : ‖f z‖ ≤ maxModulus f R := norm_le_maxModulus_on_circle f hf_entire.continuous hzR
    have hnorm' : ‖f z‖ ≤ max 1 (maxModulus f R) := le_trans hnorm (le_max_right _ _)
    by_cases hfz : f z = 0
    · have hlogM_nonneg : 0 ≤ Real.log (max 1 (maxModulus f R)) :=
        Real.log_nonneg (le_max_left _ _)
      simpa [hfz] using hlogM_nonneg
    · have hpos : 0 < ‖f z‖ := norm_pos_iff.2 hfz
      exact Real.log_le_log hpos hnorm'
  -- Convert Jensen + `havg_le` into an upper bound on the finsum.
  have hsum_le :
      (∑ᶠ u, MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|) u * Real.log (R * ‖u‖⁻¹))
        ≤ Real.log (max 1 (maxModulus f R)) - Real.log ‖f 0‖ := by
    have := sub_le_sub_right havg_le (Real.log ‖f 0‖)
    simpa [hjensen, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
  -- Lower-bound the same finsum by `log 2 * (number of zeros with ‖u‖ ≤ R/2)`.
  let D : Function.locallyFinsuppWithin (closedBall (0 : ℂ) |R|) ℤ :=
    MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|)
  have hD_fin : (D.support : Set ℂ).Finite := D.finiteSupport (isCompact_closedBall (0 : ℂ) |R|)
  have hD_nonneg : 0 ≤ D := by
    have hf_an : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) |R|) := by
      intro z _
      exact hf_entire.analyticAt z
    exact hf_an.divisor_nonneg
  let S : Set ℂ := {u : ℂ | u ∈ D.support ∧ ‖u‖ ≤ R / 2}
  have hS_fin : S.Finite := by
    refine hD_fin.subset ?_
    intro u hu
    exact hu.1
  have hlog2_pos : 0 < Real.log 2 := by
    simpa using (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  -- This block is copied from `card_zeros_le_of_maxModulus`, with only the `hsum_le` bound changed.
  have hsum_ge :
      (Real.log 2) * (hS_fin.toFinset.card : ℝ)
        ≤ (∑ᶠ u, D u * Real.log (R * ‖u‖⁻¹)) := by
    -- Expand the finsum as a finite sum over the support.
    have hsupp :
        (Function.support fun u => (D u : ℝ) * Real.log (R * ‖u‖⁻¹)) ⊆ hD_fin.toFinset := by
      intro u hu
      have ht_ne : (D u : ℝ) * Real.log (R * ‖u‖⁻¹) ≠ 0 := (Function.mem_support.1 hu)
      have hDu : D u ≠ 0 := by
        intro hDu0
        apply ht_ne
        simp [hDu0]
      have huD : u ∈ D.support := by
        have : u ∈ Function.support (fun x : ℂ => D x) := (Function.mem_support.2 hDu)
        simpa [Function.locallyFinsuppWithin.support] using this
      exact hD_fin.mem_toFinset.2 huD
    have hsum_eq :
        (∑ᶠ u, D u * Real.log (R * ‖u‖⁻¹))
          = ∑ u ∈ hD_fin.toFinset, (D u : ℝ) * Real.log (R * ‖u‖⁻¹) := by
      classical
      -- `finsum` over a finite-support function is a finite sum over the support.
      simpa using finsum_eq_sum_of_support_subset
        (f := fun u : ℂ => (D u : ℝ) * Real.log (R * ‖u‖⁻¹))
        (s := hD_fin.toFinset) hsupp
    -- Lower bound each term by `log 2` on `S`.
    have hterm_ge :
        ∀ u ∈ hS_fin.toFinset, (Real.log 2) ≤ (D u : ℝ) * Real.log (R * ‖u‖⁻¹) := by
      intro u hu
      have huS : u ∈ S := hS_fin.mem_toFinset.1 hu
      have hu_support : u ∈ D.support := huS.1
      have hDu_ne : D u ≠ 0 := by
        intro hDu0
        exact hu_support (by simp [hDu0])
      have hDu_pos : (0 : ℤ) < D u := by
        have hDu0 : (0 : ℤ) ≤ D u := hD_nonneg u
        exact lt_of_le_of_ne hDu0 (Ne.symm hDu_ne)
      have hu_ne0 : u ≠ 0 := by
        intro hu0
        have : D 0 = 0 := by simpa [D] using hdiv0
        have : D u = 0 := by simpa [hu0] using this
        exact hDu_ne this
      have hu_le : ‖u‖ ≤ R / 2 := huS.2
      have hu_pos : 0 < ‖u‖ := norm_pos_iff.2 hu_ne0
      have htwo : (2 : ℝ) ≤ R * ‖u‖⁻¹ := by
        have hmul : (2 : ℝ) * ‖u‖ ≤ R := by nlinarith
        have : (2 : ℝ) ≤ R / ‖u‖ := (le_div_iff₀ hu_pos).2 hmul
        simpa [div_eq_mul_inv] using this
      have hlog_ge : Real.log 2 ≤ Real.log (R * ‖u‖⁻¹) :=
        Real.log_le_log (by positivity : (0 : ℝ) < 2) htwo
      have hlog_nonneg : 0 ≤ Real.log (R * ‖u‖⁻¹) := by
        have h1 : (1 : ℝ) ≤ R * ‖u‖⁻¹ := le_trans (by norm_num : (1 : ℝ) ≤ 2) htwo
        exact Real.log_nonneg h1
      have hDu_ge1 : (1 : ℝ) ≤ (D u : ℝ) := by exact_mod_cast hDu_pos
      have hlog_ge' : (Real.log 2 : ℝ) ≤ (1 : ℝ) * Real.log (R * ‖u‖⁻¹) := by
        simpa [one_mul] using hlog_ge
      have := le_trans hlog_ge' (mul_le_mul_of_nonneg_right hDu_ge1 hlog_nonneg)
      simpa [one_mul, mul_assoc] using this
    -- The sum over the whole support dominates `log2 * card S`.
    have hcard_mul :
        (Real.log 2) * (hS_fin.toFinset.card : ℝ)
          ≤ ∑ u ∈ hS_fin.toFinset, (D u : ℝ) * Real.log (R * ‖u‖⁻¹) := by
      have h :=
        mul_card_le_sum_of_forall_le (s := hS_fin.toFinset) (a := Real.log 2)
          (f := fun u => (D u : ℝ) * Real.log (R * ‖u‖⁻¹)) hterm_ge
      simpa [mul_comm] using h
    -- Enlarge from `S` to the full support by monotonicity (all terms are nonnegative).
    have hnonneg : ∀ u ∈ hD_fin.toFinset, 0 ≤ (D u : ℝ) * Real.log (R * ‖u‖⁻¹) := by
      intro u hu
      have hDu0 : (0 : ℤ) ≤ D u := hD_nonneg u
      have hDu0' : (0 : ℝ) ≤ (D u : ℝ) := by exact_mod_cast hDu0
      have hlog0 : 0 ≤ Real.log (R * ‖u‖⁻¹) := by
        have huU : u ∈ closedBall (0 : ℂ) |R| := by
          have : u ∈ D.support := hD_fin.mem_toFinset.1 hu
          exact D.supportWithinDomain this
        have hu_le : ‖u‖ ≤ |R| := by simpa [Metric.mem_closedBall, dist_eq_norm] using huU
        by_cases hu0 : u = 0
        · subst hu0
          simp
        · have hu_pos : 0 < ‖u‖ := norm_pos_iff.2 hu0
          have hmul_ge : (1 : ℝ) ≤ R * ‖u‖⁻¹ := by
            have : (1 : ℝ) ≤ R / ‖u‖ := by
              have hu_le' : ‖u‖ ≤ R := by simpa [abs_of_pos hR] using hu_le
              have : (1 : ℝ) * ‖u‖ ≤ R := by simpa [one_mul] using hu_le'
              exact (le_div_iff₀ hu_pos).2 this
            simpa [div_eq_mul_inv] using this
          exact Real.log_nonneg hmul_ge
      exact mul_nonneg hDu0' hlog0
    have hsub : hS_fin.toFinset ⊆ hD_fin.toFinset := by
      intro u hu
      have : u ∈ S := by simpa [hS_fin.mem_toFinset] using hu
      exact hD_fin.mem_toFinset.2 this.1
    have hsum_le' :
        (∑ u ∈ hS_fin.toFinset, (D u : ℝ) * Real.log (R * ‖u‖⁻¹))
          ≤ ∑ u ∈ hD_fin.toFinset, (D u : ℝ) * Real.log (R * ‖u‖⁻¹) := by
      have hnonneg' :
          ∀ u ∈ hD_fin.toFinset, u ∉ hS_fin.toFinset → 0 ≤ (D u : ℝ) * Real.log (R * ‖u‖⁻¹) := by
        intro u hu _
        exact hnonneg u hu
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg'
    have :
        (Real.log 2) * (hS_fin.toFinset.card : ℝ)
          ≤ ∑ u ∈ hD_fin.toFinset, (D u : ℝ) * Real.log (R * ‖u‖⁻¹) :=
      le_trans hcard_mul hsum_le'
    simpa [hsum_eq] using this
  -- Finish by dividing by `log 2`.
  have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt hlog2_pos
  have hcard :
      (hS_fin.toFinset.card : ℝ)
        ≤ (Real.log (max 1 (maxModulus f R)) - Real.log ‖f 0‖) / Real.log 2 := by
    have h1 :
        (Real.log 2) * (hS_fin.toFinset.card : ℝ)
          ≤ Real.log (max 1 (maxModulus f R)) - Real.log ‖f 0‖ :=
      le_trans hsum_ge hsum_le
    have := mul_le_mul_of_nonneg_left h1 (le_of_lt (inv_pos.2 hlog2_pos))
    -- rewrite `inv * (log2 * card) = card` and `inv * rhs = rhs / log2`
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hlog2_ne] using this
  have hcard' :
      ((S.ncard : ℝ)) ≤ (Real.log (max 1 (maxModulus f R)) - Real.log ‖f 0‖) / Real.log 2 := by
    simpa [Set.ncard_eq_toFinset_card S hS_fin] using hcard
  simpa [S] using hcard'

/-! ### Jensen ⇒ a bound on the sum of multiplicities (divisor weights)

The previous lemmas bound the number of *distinct* zeros in a disk by discarding multiplicities.
For multiplicity-aware Hadamard products we instead need control of
`∑ multiplicity(u)` over zeros `u` in a disk.

We express this as the sum of divisor values on the same set: for analytic functions the divisor
value at `u` is exactly the vanishing multiplicity of `f` at `u`.
-/

private theorem circleAverage_log_norm_le_log_max_one_maxModulus
    (f : ℂ → ℂ) {R : ℝ} (hR : 0 < R) (hf_entire : Differentiable ℂ f) :
    Real.circleAverage (Real.log ‖f ·‖) 0 R ≤ Real.log (max 1 (maxModulus f R)) := by
  have hmer : MeromorphicOn f (closedBall (0 : ℂ) |R|) := fun z _ =>
    (hf_entire.analyticAt z).meromorphicAt
  have hCircleInt : CircleIntegrable (Real.log ‖f ·‖) 0 R := by
    apply MeromorphicOn.circleIntegrable_log_norm
    intro z hz
    have hz' : z ∈ closedBall (0 : ℂ) |R| := Metric.sphere_subset_closedBall hz
    exact hmer z hz'
  refine
    Real.circleAverage_mono_on_of_le_circle (c := (0 : ℂ)) (R := R)
      (f := fun z => Real.log ‖f z‖) (a := Real.log (max 1 (maxModulus f R))) hCircleInt ?_
  intro z hz
  have hzR : ‖z‖ = R := by simpa [Metric.mem_sphere, dist_eq_norm, abs_of_pos hR] using hz
  have hnorm : ‖f z‖ ≤ maxModulus f R := norm_le_maxModulus_on_circle f hf_entire.continuous hzR
  have hnorm' : ‖f z‖ ≤ max 1 (maxModulus f R) := le_trans hnorm (le_max_right _ _)
  by_cases hfz : f z = 0
  · have hlogM_nonneg : 0 ≤ Real.log (max 1 (maxModulus f R)) :=
      Real.log_nonneg (le_max_left _ _)
    simpa [hfz] using hlogM_nonneg
  · have hpos : 0 < ‖f z‖ := norm_pos_iff.2 hfz
    exact Real.log_le_log hpos hnorm'

/-- Jensen-style bound on the sum of divisor weights in the disk `‖u‖ ≤ R/2`.

This is the multiplicity-aware analogue of `card_zeros_le_of_max_one_maxModulus`.

The LHS is `∑_{u : ‖u‖ ≤ R/2} ord_u(f)` where `ord_u(f)` is the (nonnegative) divisor value.
-/
theorem sum_zeros_multiplicity_le_of_max_one_maxModulus (f : ℂ → ℂ) {R : ℝ} (hR : 0 < R)
    (hf_entire : Differentiable ℂ f) (hf0 : f 0 ≠ 0) :
    (∑ᶠ u : ℂ,
        if ‖u‖ ≤ R / 2 then
          ((MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|) u : ℤ) : ℝ)
        else 0)
      ≤ (Real.log (max 1 (maxModulus f R)) - Real.log ‖f 0‖) / Real.log 2 := by
  classical
  -- Setup Jensen on `closedBall 0 R`.
  have hmer : MeromorphicOn f (closedBall (0 : ℂ) |R|) := fun z _ =>
    (hf_entire.analyticAt z).meromorphicAt
  have hCB0 : (0 : ℂ) ∈ closedBall (0 : ℂ) |R| := by
    simp [Metric.mem_closedBall, abs_nonneg R]
  have htrailing : meromorphicTrailingCoeffAt f 0 = f 0 := by
    simpa using (hf_entire.analyticAt 0).meromorphicTrailingCoeffAt_of_ne_zero hf0
  have hdiv0 : MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|) 0 = 0 := by
    have horder0 : analyticOrderAt f 0 = 0 :=
      (hf_entire.analyticAt 0).analyticOrderAt_eq_zero.2 hf0
    have hmerOrder0 : meromorphicOrderAt f 0 = 0 := by
      simpa [horder0] using (hf_entire.analyticAt 0).meromorphicOrderAt_eq
    simp [MeromorphicOn.divisor_apply hmer hCB0, hmerOrder0]
  -- Jensen formula at the origin.
  have hjensen :
      Real.circleAverage (Real.log ‖f ·‖) 0 R =
        (∑ᶠ u, MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|) u * Real.log (R * ‖u‖⁻¹)) +
          Real.log ‖f 0‖ := by
    have :=
      MeromorphicOn.circleAverage_log_norm (c := (0 : ℂ)) (R := R) (f := f) (by exact hR.ne') hmer
    simpa [hdiv0, htrailing, norm_sub_rev, add_assoc, add_left_comm, add_comm, sub_eq_add_neg]
      using this
  -- Upper-bound the circle average by `log (max 1 (maxModulus f R))`.
  have havg_le := circleAverage_log_norm_le_log_max_one_maxModulus f hR hf_entire
  -- Convert Jensen + `havg_le` into an upper bound on the finsum.
  have hsum_le :
      (∑ᶠ u, MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|) u * Real.log (R * ‖u‖⁻¹))
        ≤ Real.log (max 1 (maxModulus f R)) - Real.log ‖f 0‖ := by
    have := sub_le_sub_right havg_le (Real.log ‖f 0‖)
    simpa [hjensen, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
  -- Lower-bound the same finsum by `log 2 * (sum of divisor weights in ‖u‖ ≤ R/2)`.
  let D : Function.locallyFinsuppWithin (closedBall (0 : ℂ) |R|) ℤ :=
    MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|)
  have hD_fin : (D.support : Set ℂ).Finite :=
    D.finiteSupport (isCompact_closedBall (0 : ℂ) |R|)
  have hD_nonneg : 0 ≤ D := by
    have hf_an : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) |R|) := by
      intro z _
      exact hf_entire.analyticAt z
    exact hf_an.divisor_nonneg
  let S : Set ℂ := {u : ℂ | u ∈ D.support ∧ ‖u‖ ≤ R / 2}
  have hS_fin : S.Finite := by
    refine hD_fin.subset ?_
    intro u hu
    exact hu.1
  have hlog2_pos : 0 < Real.log 2 := by
    simpa using (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt hlog2_pos
  have hsum_ge :
      (Real.log 2) * (∑ u ∈ hS_fin.toFinset, ((D u : ℤ) : ℝ))
        ≤ (∑ᶠ u, D u * Real.log (R * ‖u‖⁻¹)) := by
    -- Expand the finsum as a finite sum over the support.
    have hsupp :
        (Function.support fun u => (D u : ℝ) * Real.log (R * ‖u‖⁻¹)) ⊆ hD_fin.toFinset := by
      intro u hu
      have ht_ne : (D u : ℝ) * Real.log (R * ‖u‖⁻¹) ≠ 0 := (Function.mem_support.1 hu)
      have hDu : D u ≠ 0 := by
        intro hDu0
        apply ht_ne
        simp [hDu0]
      have huD : u ∈ D.support := by
        have : u ∈ Function.support (fun x : ℂ => D x) := (Function.mem_support.2 hDu)
        simpa [Function.locallyFinsuppWithin.support] using this
      exact hD_fin.mem_toFinset.2 huD
    have hsum_eq :
        (∑ᶠ u, D u * Real.log (R * ‖u‖⁻¹)) =
          ∑ u ∈ hD_fin.toFinset, (D u : ℝ) * Real.log (R * ‖u‖⁻¹) := by
      classical
      simpa using finsum_eq_sum_of_support_subset
        (f := fun u : ℂ => (D u : ℝ) * Real.log (R * ‖u‖⁻¹))
        (s := hD_fin.toFinset) hsupp
    -- For `u ∈ S`, we have `log 2 ≤ log (R/‖u‖)`.
    have hlog_ge :
        ∀ u, u ∈ hS_fin.toFinset → Real.log 2 ≤ Real.log (R * ‖u‖⁻¹) := by
      intro u hu
      have huS : u ∈ S := hS_fin.mem_toFinset.1 hu
      have hu_ne0 : u ≠ 0 := by
        intro hu0
        have : D 0 = 0 := by simpa [D] using hdiv0
        have : D u = 0 := by simpa [hu0] using this
        have huD : u ∈ D.support := huS.1
        have huD' : u ∈ Function.support (fun x : ℂ => D x) := by
          simpa [Function.locallyFinsuppWithin.support] using huD
        exact (Function.mem_support.1 huD') this
      have hu_le : ‖u‖ ≤ R / 2 := huS.2
      have hu_pos : 0 < ‖u‖ := norm_pos_iff.2 hu_ne0
      have htwo : (2 : ℝ) ≤ R * ‖u‖⁻¹ := by
        have hmul : (2 : ℝ) * ‖u‖ ≤ R := by nlinarith
        have : (2 : ℝ) ≤ R / ‖u‖ := (le_div_iff₀ hu_pos).2 hmul
        simpa [div_eq_mul_inv] using this
      exact Real.log_le_log (by positivity : (0 : ℝ) < 2) htwo
    -- Now sum the pointwise inequality `log2 * D u ≤ D u * log(...)` over `S`.
    have hS_term :
        (Real.log 2) * (∑ u ∈ hS_fin.toFinset, ((D u : ℤ) : ℝ))
          ≤ ∑ u ∈ hS_fin.toFinset, (D u : ℝ) * Real.log (R * ‖u‖⁻¹) := by
      -- Rewrite the LHS as a sum.
      have hmul_sum :
          (Real.log 2) * (∑ u ∈ hS_fin.toFinset, ((D u : ℤ) : ℝ)) =
            ∑ u ∈ hS_fin.toFinset, (Real.log 2) * ((D u : ℤ) : ℝ) := by
        simp [Finset.mul_sum]
      rw [hmul_sum]
      refine Finset.sum_le_sum ?_
      intro u hu
      have hDu0 : (0 : ℤ) ≤ D u := hD_nonneg u
      have hDu0' : (0 : ℝ) ≤ (D u : ℝ) := by exact_mod_cast hDu0
      have hlog_nonneg : 0 ≤ Real.log (R * ‖u‖⁻¹) :=
        le_trans (le_of_lt hlog2_pos) (hlog_ge u hu)
      have hle : (Real.log 2) ≤ Real.log (R * ‖u‖⁻¹) := hlog_ge u hu
      -- Multiply by the nonnegative weight `(D u : ℝ)`.
      have := mul_le_mul_of_nonneg_left hle hDu0'
      -- Coerce `(D u : ℤ)` to `ℝ` consistently.
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    -- Enlarge from `S` to the full support finset (all terms are nonnegative).
    have hnonneg : ∀ u ∈ hD_fin.toFinset, 0 ≤ (D u : ℝ) * Real.log (R * ‖u‖⁻¹) := by
      intro u hu
      have hDu0 : (0 : ℤ) ≤ D u := hD_nonneg u
      have hDu0' : (0 : ℝ) ≤ (D u : ℝ) := by exact_mod_cast hDu0
      have hlog0 : 0 ≤ Real.log (R * ‖u‖⁻¹) := by
        -- `u` is in the support of `D`, hence `u ∈ closedBall 0 R`, so `‖u‖ ≤ R`.
        have huU : u ∈ closedBall (0 : ℂ) |R| := by
          have : u ∈ D.support := hD_fin.mem_toFinset.1 hu
          exact D.supportWithinDomain this
        have hu_le : ‖u‖ ≤ |R| := by simpa [Metric.mem_closedBall, dist_eq_norm] using huU
        by_cases hu0 : u = 0
        · subst hu0
          simp
        · have hu_pos : 0 < ‖u‖ := norm_pos_iff.2 hu0
          have hmul_ge : (1 : ℝ) ≤ R * ‖u‖⁻¹ := by
            have : (1 : ℝ) ≤ R / ‖u‖ := by
              have hu_le' : ‖u‖ ≤ R := by simpa [abs_of_pos hR] using hu_le
              have : (1 : ℝ) * ‖u‖ ≤ R := by simpa [one_mul] using hu_le'
              exact (le_div_iff₀ hu_pos).2 this
            simpa [div_eq_mul_inv] using this
          exact Real.log_nonneg hmul_ge
      exact mul_nonneg hDu0' hlog0
    have hsub : hS_fin.toFinset ⊆ hD_fin.toFinset := by
      intro u hu
      have : u ∈ S := by simpa [hS_fin.mem_toFinset] using hu
      exact hD_fin.mem_toFinset.2 this.1
    have hsum_le' :
        (∑ u ∈ hS_fin.toFinset, (D u : ℝ) * Real.log (R * ‖u‖⁻¹))
          ≤ ∑ u ∈ hD_fin.toFinset, (D u : ℝ) * Real.log (R * ‖u‖⁻¹) := by
      have hnonneg' :
          ∀ u ∈ hD_fin.toFinset, u ∉ hS_fin.toFinset → 0 ≤ (D u : ℝ) * Real.log (R * ‖u‖⁻¹) := by
        intro u hu _
        exact hnonneg u hu
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg'
    have :
        (Real.log 2) * (∑ u ∈ hS_fin.toFinset, ((D u : ℤ) : ℝ))
          ≤ ∑ u ∈ hD_fin.toFinset, (D u : ℝ) * Real.log (R * ‖u‖⁻¹) :=
      le_trans hS_term hsum_le'
    simpa [hsum_eq] using this
  -- Divide by `log 2`.
  have hweight :
      (∑ u ∈ hS_fin.toFinset, ((D u : ℤ) : ℝ))
        ≤ (Real.log (max 1 (maxModulus f R)) - Real.log ‖f 0‖) / Real.log 2 := by
    have h1 :
        (Real.log 2) * (∑ u ∈ hS_fin.toFinset, ((D u : ℤ) : ℝ))
          ≤ Real.log (max 1 (maxModulus f R)) - Real.log ‖f 0‖ :=
      le_trans hsum_ge hsum_le
    have := mul_le_mul_of_nonneg_left h1 (le_of_lt (inv_pos.2 hlog2_pos))
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hlog2_ne] using this
  -- Unfold the set definition in the statement.
  -- Rewrite the LHS as a `finsum` cutoff.
  have h_finsum :
      (∑ᶠ u : ℂ, if ‖u‖ ≤ R / 2 then ((D u : ℤ) : ℝ) else 0) =
        ∑ u ∈ hS_fin.toFinset, ((D u : ℤ) : ℝ) := by
    -- The support is contained in `S`.
    have hsupp :
        Function.support (fun u : ℂ => if ‖u‖ ≤ R / 2 then ((D u : ℤ) : ℝ) else 0)
          ⊆ hS_fin.toFinset := by
      intro u hu
      have hu_ne : (if ‖u‖ ≤ R / 2 then ((D u : ℤ) : ℝ) else 0) ≠ 0 :=
        Function.mem_support.1 hu
      have hu_le : ‖u‖ ≤ R / 2 := by
        by_contra hle
        apply hu_ne
        simp [hle]
      have hDu : D u ≠ 0 := by
        intro hDu0
        apply hu_ne
        simp [hu_le, hDu0]
      have huS : u ∈ S := by
        refine ⟨?_, hu_le⟩
        have : u ∈ Function.support (fun x : ℂ => D x) := Function.mem_support.2 hDu
        simpa [Function.locallyFinsuppWithin.support] using this
      exact hS_fin.mem_toFinset.2 huS
    have :=
      (finsum_eq_sum_of_support_subset
        (f := fun u : ℂ => if ‖u‖ ≤ R / 2 then ((D u : ℤ) : ℝ) else 0)
        (s := hS_fin.toFinset) hsupp)
    -- Now simplify the `if` on the RHS using membership in `S`.
    have hsum_if :
        (∑ u ∈ hS_fin.toFinset, if ‖u‖ ≤ R / 2 then ((D u : ℤ) : ℝ) else 0) =
          ∑ u ∈ hS_fin.toFinset, ((D u : ℤ) : ℝ) := by
      refine Finset.sum_congr rfl ?_
      intro u hu
      have huS : u ∈ S := hS_fin.mem_toFinset.1 hu
      have hu_le : ‖u‖ ≤ R / 2 := huS.2
      simp [hu_le]
    simpa [hsum_if] using this
  -- Now finish by rewriting both sides to the theorem statement.
  have hweight' :
      (∑ᶠ u : ℂ, if ‖u‖ ≤ R / 2 then ((D u : ℤ) : ℝ) else 0)
        ≤ (Real.log (max 1 (maxModulus f R)) - Real.log ‖f 0‖) / Real.log 2 := by
    simpa [h_finsum] using hweight
  simpa [D] using hweight'

end ZeroCounting

end Hadamard
