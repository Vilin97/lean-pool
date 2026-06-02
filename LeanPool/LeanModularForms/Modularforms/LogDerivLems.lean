/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.Modularforms.Tendstolems
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
import Mathlib.Topology.Separation.CompletelyRegular

/-! # LogDerivLems -/



open  TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat


theorem logDeriv_tprod_eq_tsum2 {s : Set ℂ} (hs : IsOpen s) (x : s) (f : ℕ → ℂ → ℂ)
    (hf : ∀ i, f i x ≠ 0)
    (hd : ∀ i : ℕ, DifferentiableOn ℂ (f i) s) (hm : Summable fun i ↦ logDeriv (f i) ↑x)
    (htend : MultipliableLocallyUniformlyOn f s) (hnez : ∏' (i : ℕ), f i ↑x ≠ 0) :
    logDeriv (∏' i : ℕ, f i ·) x = ∑' i : ℕ, logDeriv (f i) x := by
    have h2 := Summable.hasSum hm
    rw [Summable.hasSum_iff_tendsto_nat hm] at h2
    apply symm
    rw [← Summable.hasSum_iff hm]
    rw [Summable.hasSum_iff_tendsto_nat hm]
    let g := (∏' i : ℕ, f i ·)
    have h_tlu : TendstoLocallyUniformlyOn (fun n z ↦ ∏ i ∈ Finset.range n, f i z) g atTop s := by
      have := htend.hasProdLocallyUniformlyOn.tendstoLocallyUniformlyOn_finsetRange
      exact this.congr (fun n => by
        intro z _; change ∏ i ∈ Finset.range n, f i z = ∏ i ∈ Finset.range n, f i z; rfl)
    have h_diff :
        ∀ᶠ (n : ℕ) in atTop, DifferentiableOn ℂ (fun z => ∏ i ∈ Finset.range n, f i z) s := by
      simp only [eventually_atTop, ge_iff_le]
      use 0; intro b _ z hz
      have := DifferentiableAt.finsetProd (fun i (_ : i ∈ Finset.range b) =>
        (hd i z hz).differentiableAt (IsOpen.mem_nhds hs hz))
      exact this.differentiableWithinAt.congr (fun w hw => (Finset.prod_apply ..).symm)
        (Finset.prod_apply ..).symm
    have HT := logDeriv_tendsto (f := fun (n : ℕ) z ↦ ∏ i ∈ Finset.range n, f i z) (g := g)
      (s := s) hs (x.2) (p := atTop) h_tlu h_diff hnez
    conv =>
      enter [1]
      ext n
      rw [← logDeriv_prod (by intro i hi; apply hf i)
        (by intro i hi; apply (hd i x x.2).differentiableAt; exact IsOpen.mem_nhds hs x.2)]
    exact HT


theorem logDeriv_tprod_eq_tsumold {s : Set ℂ} (hs : IsOpen s) (x : s) (f : ℕ → ℂ → ℂ)
    (hf : ∀ i, f i x ≠ 0)
    (hd : ∀ i : ℕ, DifferentiableOn ℂ (f i) s) (hm : Summable fun i ↦ logDeriv (f i) ↑x)
    (htend : TendstoLocallyUniformlyOn (fun n ↦ ∏ i ∈ Finset.range n, f i)
    (fun x ↦ ∏' (i : ℕ), f i x) atTop s) (hnez : ∏' (i : ℕ), f i ↑x ≠ 0) :
    logDeriv (∏' i : ℕ, f i ·) x = ∑' i : ℕ, logDeriv (f i) x := by
    have h2 := Summable.hasSum hm
    rw [Summable.hasSum_iff_tendsto_nat hm] at h2
    apply symm
    rw [← Summable.hasSum_iff hm]
    rw [Summable.hasSum_iff_tendsto_nat hm]
    let g := (∏' i : ℕ, f i ·)
    have HT := logDeriv_tendsto (f := fun n ↦ ∏ i ∈ Finset.range n, (f i)) (g := g)
      (s := s) hs (x.2) (p := atTop) ?_ ?_ ?_
    · conv =>
        enter [1]
        ext n
        rw [← logDeriv_prod (by intro i hi; apply hf i)
          (by intro i hi; apply (hd i x x.2).differentiableAt; exact IsOpen.mem_nhds hs x.2)]
      apply HT.congr
      intro m
      congr
      ext i
      simp only [Finset.prod_apply]
    · exact htend
    · simp only [eventually_atTop, ge_iff_le]
      use 0
      intro b hb
      rw [DifferentiableOn]
      intro z hz
      apply DifferentiableAt.differentiableWithinAt
      have hp : ∀ (i : ℕ), i ∈ Finset.range b →  DifferentiableAt ℂ (f i) z := by
        intro i hi
        have := (hd i z hz).differentiableAt
        apply this
        exact IsOpen.mem_nhds hs hz
      have := DifferentiableAt.finsetProd hp
      convert this
    · exact hnez


lemma logDeriv_one_sub_exp (r : ℂ) : logDeriv (fun z => 1 - r * cexp (z)) =
    fun z => -r * cexp z / (1 - r * cexp ( z)) := by
  ext z
  rw [logDeriv]
  simp only [Pi.div_apply, differentiableAt_const, differentiableAt_exp, DifferentiableAt.fun_mul,
    deriv_fun_sub, deriv_const', deriv_fun_mul, zero_mul, Complex.deriv_exp, zero_add, zero_sub,
    neg_mul]

lemma logDeriv_one_sub_exp_comp (r : ℂ) (g : ℂ → ℂ) (hg : Differentiable ℂ g) :
    logDeriv ((fun z => 1 - r * cexp (z)) ∘ g) =
    fun z => -r * ((deriv g) z) * cexp (g z) / (1 - r * cexp (g (z))) := by
  ext y
  rw  [logDeriv_comp, logDeriv_one_sub_exp]
  · simp only [neg_mul]
    ring
  · simp only [differentiableAt_const, differentiableAt_exp, DifferentiableAt.fun_mul,
      DifferentiableAt.fun_sub]
  · exact hg y

lemma logDeriv_q_expo_summable (r : ℂ) (hr : ‖r‖ < 1) : Summable fun n : ℕ =>
    (n * r^n / (1 - r^n)) := by
  have := aux47 r hr
  have h1 : Tendsto (fun n : ℕ => (1 : ℂ)) atTop (𝓝 1) := by simp
  have h2 := Filter.Tendsto.div h1 this (by simp)
  rw [Metric.tendsto_atTop] at h2
  simp only [gt_iff_lt, ge_iff_le, Pi.div_apply, one_div, ne_eq, one_ne_zero, not_false_eq_true,
    div_self, dist_eq_norm] at h2
  have h3 := h2 1 (by norm_num)
  apply Summable.of_norm_bounded_eventually_nat (g := fun n => 2 * ‖n * r^n‖)
  · apply Summable.mul_left
    simp only [Complex.norm_mul, RCLike.norm_natCast, norm_pow]
    have := (summable_norm_pow_mul_geometric_of_norm_lt_one 1 hr)
    simp only [pow_one, Complex.norm_mul, RCLike.norm_natCast, norm_pow] at this
    apply this
  · simp only [Complex.norm_div, Complex.norm_mul, RCLike.norm_natCast, norm_pow, eventually_atTop,
    ge_iff_le]
    obtain ⟨N, hN⟩ := h3
    use N
    intro n hn
    have h4 := hN n hn
    have : dist ((1 - r ^ n)⁻¹) 1 < 1 := by rwa [dist_eq_norm]
    have := norm_lt_of_mem_ball (Metric.mem_ball.mpr this) (E := ℂ)
    simp only [tendsto_const_nhds_iff, norm_inv, one_mem, CStarRing.norm_of_mem_unitary,
      ge_iff_le] at *
    rw [div_eq_mul_inv]
    rw [mul_comm]
    gcongr
    apply le_trans this.le
    norm_cast

lemma func_div (a b c d : ℂ → ℂ) (x : ℂ) (hb : b x ≠ 0) (hd : d x ≠ 0) :
     (a / b) x = (c /d) x ↔ (a * d) x = (b * c) x := by
  constructor
  · intro h
    simp only [ne_eq, Pi.div_apply, Pi.mul_apply] at *
    rw [div_eq_div_iff hb hd] at h
    nth_rw 2 [mul_comm]
    exact h
  · intro h
    simp only [Pi.div_apply]
    rw [div_eq_div_iff hb hd]
    simp only [Pi.mul_apply] at h
    nth_rw 2 [mul_comm]
    exact h


variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

lemma deriv_EqOn_congr {f g : ℂ → ℂ} (s : Set ℂ) (hfg : s.EqOn f g) (hs : IsOpen s) :
    s.EqOn (deriv f) ( deriv g) := by
  intro x hx
  rw [← derivWithin_of_isOpen hs hx]
  rw [← derivWithin_of_isOpen hs hx]
  apply derivWithin_congr hfg
  apply hfg hx


lemma logDeriv_eqOn_iff2 (f g : ℂ → ℂ) (s : Set ℂ) (hf : DifferentiableOn ℂ f s)
    (hg : DifferentiableOn ℂ g s) (_hs : s.Nonempty) (hs2 : IsOpen s) (hsc : Convex ℝ s)
    (hgn : ∀ x, x ∈ s → g x ≠ 0) (hfn : ∀ x, x ∈ s → f x ≠ 0) : EqOn (logDeriv f) (logDeriv g) s ↔
    ∃( z : ℂ),  z ≠ 0 ∧  EqOn (f) (z • g) s := by
  haveI : IsBoundedSMul ℝ ℂ := NormedSpace.toIsBoundedSMul
  exact logDeriv_eqOn_iff hf hg hs2 (hsc.isPreconnected) hgn hfn
