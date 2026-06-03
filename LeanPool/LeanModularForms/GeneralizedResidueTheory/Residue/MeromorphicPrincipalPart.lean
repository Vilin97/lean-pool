/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.GeneralizedResidueTheory.Residue.GeneralizedTheoremBase
import LeanPool.LeanModularForms.GeneralizedResidueTheory.CauchyPrimitive
-- Note: Does NOT import FlatnessTransfer to avoid circular dependencies.
-- The zpow FTC lemmas used here are reproved locally.
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Meromorphic Laurent Principal Parts

This file connects `MeromorphicAt` from Mathlib with Laurent principal parts and
proves that contour integrals of principal parts with zero residue vanish on
closed curves.

## Main Definitions

* `meromorphicPrincipalPart` -- the finite-rank polar part of a meromorphic function

## Main Results

* `meromorphicPrincipalPart_differentiableOn` -- principal part is differentiable away from the pole
* `meromorphicAt_sub_principalPart_eventually` -- f minus its principal part is analytic at the pole
* `contourIntegral_zpow_eq_zero` -- contour integral of (z-s)^n dz = 0 for n <= -2 on closed curves
* `contourIntegral_principalPart_eq_zero_of_residue_zero` -- contour integral of pp = 0 when
  residue is zero

## Mathematical Overview

For a function `f` meromorphic at `s` with a pole of order `N`, Mathlib gives a
decomposition `f =ae (z - s)^(-N) * g` near `s` with `g` analytic and `g(s) != 0`.
The principal part is the sum of the first `N` terms of the Laurent series:

  pp(z) = sum_{k=1}^{N} c_k / (z - s)^k

where `c_k = (1/k!) * iteratedDeriv k g s` (adjusted by the order).

When `Res(f, s) = 0`, the `(z-s)^{-1}` coefficient vanishes, and each `(z-s)^{-k}`
term for `k >= 2` integrates to zero on closed curves (by FTC). So the contour integral
of pp = 0.

## References

* Mathlib `MeromorphicAt`, `meromorphicOrderAt`
-/

open Complex MeasureTheory Set Filter Topology Metric
open scoped Real Interval

attribute [local instance] Classical.propDecidable

noncomputable section

namespace GeneralizedResidueTheory

/-! ### Definition of the meromorphic principal part

For `f` meromorphic at `s`, the principal part extracts the finite Laurent tail.
If `meromorphicOrderAt f s = -N` (pole of order N), we use the Mathlib decomposition
`f =ae (z - s)^(-N) * g` with `g` analytic and `g(s) != 0`, then:

  pp(z) = sum_{k=0}^{N-1} (g^(k)(s) / k!) * (z - s)^{k - N}

This equals `sum_{j=1}^{N} c_j / (z-s)^j` where `c_j = g^{(N-j)}(s) / (N-j)!`.

If `f` is analytic at `s` (order >= 0) or not meromorphic, the principal part is 0. -/

/-- Helper: extract the pole order as a natural number from meromorphic data. -/
private noncomputable def poleOrderNat (f : ℂ → ℂ) (s : ℂ) : ℕ :=
  (-(meromorphicOrderAt f s).untop₀).toNat

/-- Helper: extract the analytic factor g from the meromorphic decomposition. -/
private noncomputable def meromorphicFactor (f : ℂ → ℂ) (s : ℂ)
    (hf : MeromorphicAt f s) (hne : meromorphicOrderAt f s ≠ ⊤) : ℂ → ℂ :=
  ((meromorphicOrderAt_ne_top_iff hf).mp hne).choose

/-- The meromorphic principal part of `f` at `s`.

If `f` has a pole of order `N` at `s` (i.e., `meromorphicOrderAt f s = -(N : ℤ)` with N > 0),
the principal part is a rational function that captures the singular behavior.
If `f` is analytic at `s` or not meromorphic, returns 0. -/
noncomputable def meromorphicPrincipalPart (f : ℂ → ℂ) (s : ℂ) : ℂ → ℂ :=
  if h : MeromorphicAt f s ∧ meromorphicOrderAt f s < 0 then
    fun z => (Finset.range (poleOrderNat f s)).sum fun k =>
      (iteratedDeriv k (meromorphicFactor f s h.1 h.2.ne_top) s /
        ↑(Nat.factorial k)) * (z - s) ^ ((k : ℤ) - (poleOrderNat f s : ℤ))
  else
    fun _ => 0

/-- When `f` is analytic at `s` (non-negative order), the principal part is zero. -/
theorem meromorphicPrincipalPart_eq_zero_of_analyticAt (f : ℂ → ℂ) (s : ℂ)
    (hf : AnalyticAt ℂ f s) :
    meromorphicPrincipalPart f s = fun _ => 0 := by
  unfold meromorphicPrincipalPart
  have h_ord : 0 ≤ meromorphicOrderAt f s := hf.meromorphicOrderAt_nonneg
  exact dif_neg (fun h => absurd h.2 (not_lt.mpr h_ord))

/-! ### Differentiability of the principal part -/

/-- Each term `c * (z - s)^n` with `n < 0` is differentiable away from `s`. -/
private theorem differentiableOn_zpow_sub_compl (s : ℂ) (n : ℤ) (c : ℂ) :
    DifferentiableOn ℂ (fun z => c * (z - s) ^ n) {s}ᶜ := by
  intro z hz
  have hne : z - s ≠ 0 := sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hz)
  apply DifferentiableAt.differentiableWithinAt
  exact (differentiableAt_const c).mul
    ((differentiableAt_id.sub (differentiableAt_const s)).zpow (Or.inl hne))

/-- The principal part is differentiable on `{s}ᶜ`. -/
theorem meromorphicPrincipalPart_differentiableOn (f : ℂ → ℂ) (s : ℂ)
    (hf : MeromorphicAt f s) :
    DifferentiableOn ℂ (meromorphicPrincipalPart f s) {s}ᶜ := by
  unfold meromorphicPrincipalPart
  by_cases h_neg : meromorphicOrderAt f s < 0
  · rw [dif_pos ⟨hf, h_neg⟩]
    apply DifferentiableOn.fun_sum
    intro k _
    exact differentiableOn_zpow_sub_compl s _ _
  · rw [dif_neg (not_and_of_not_right _ h_neg)]
    exact differentiableOn_const 0

/-- When the meromorphic order is negative, `poleOrderNat` is positive. -/
private theorem poleOrderNat_pos_of_neg_order (f : ℂ → ℂ) (s : ℂ)
    (h_neg : meromorphicOrderAt f s < 0) : 0 < poleOrderNat f s := by
  change 0 < (-(meromorphicOrderAt f s).untop₀).toNat
  have h_neg' : (meromorphicOrderAt f s).untop₀ < 0 := by
    cases h : (meromorphicOrderAt f s) with
    | top => exact absurd h h_neg.ne_top
    | coe v =>
      simp only [WithTop.untop₀, WithTop.untopD, WithTop.recTopCoe]
      rw [h] at h_neg; exact_mod_cast h_neg
  omega

/-! ### The regular part is analytic

f minus its principal part extends analytically to the pole. -/

/-- Taylor remainder factorization: if `G` is analytic at `s` and `P` is the
truncated Taylor polynomial `Σ_{k<N} (G^(k)(s)/k!) * (z-s)^k`, then
`G - P = (z-s)^N • H` near `s` for some analytic `H`. -/
private theorem taylor_remainder_factored (G : ℂ → ℂ) (s : ℂ) (N : ℕ)
    (hG_an : AnalyticAt ℂ G s) (P : ℂ → ℂ)
    (hP_def : P = fun z => ∑ k ∈ Finset.range N,
      (iteratedDeriv k G s / ↑(k.factorial)) * (z - s) ^ (k : ℕ))
    (hP_an : AnalyticAt ℂ P s) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H s ∧
      ∀ᶠ z in 𝓝 s, G z - P z = (z - s) ^ N • H z := by
  exact (natCast_le_analyticOrderAt (hG_an.sub hP_an)).mp (by
    rw [natCast_le_analyticOrderAt (hG_an.sub hP_an)]
    have hG_fps := hG_an.hasFPowerSeriesAt
    set pG := FormalMultilinearSeries.ofScalars ℂ
      (fun n => iteratedDeriv n G s / ↑(n.factorial)) with hpG_def
    have hH_fps := HasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope N hG_fps
    set H := (Function.swap dslope s)^[N] G
    refine ⟨H, hH_fps.analyticAt, ?_⟩
    filter_upwards [hasFPowerSeriesAt_iff'.mp hG_fps,
      hasFPowerSeriesAt_iff'.mp hH_fps] with z hG_z hH_z
    simp only [FormalMultilinearSeries.coeff_iterate_fslope, smul_eq_mul] at hG_z hH_z
    change G z - P z = (z - s) ^ N * H z
    set c := fun k => (z - s) ^ k * pG.coeff k with hc_def
    have hG_tail : HasSum (fun j => c (j + N))
        (G z - ∑ i ∈ Finset.range N, c i) :=
      (hasSum_nat_add_iff' N).mpr hG_z
    have hP_eq : P z = ∑ i ∈ Finset.range N, c i := by
      rw [hP_def]
      simp only [c, pG, FormalMultilinearSeries.coeff_ofScalars]
      congr 1; ext k; ring
    rw [hP_eq]
    rw [← hG_tail.tsum_eq]
    rw [← hH_z.tsum_eq, ← tsum_mul_left]
    congr 1; ext j
    simp only [c]
    ring)

/-- If `f` is meromorphic at `s`, then `f - meromorphicPrincipalPart f s` agrees
with an analytic function near `s` (away from `s`). Since the principal part
captures exactly the singular behavior, the difference extends analytically. -/
theorem meromorphicAt_sub_principalPart_eventually (f : ℂ → ℂ) (s : ℂ)
    (hf : MeromorphicAt f s) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g s ∧
      ∀ᶠ z in 𝓝[≠] s, f z - meromorphicPrincipalPart f s z = g z := by
  by_cases h_neg : meromorphicOrderAt f s < 0
  · set N := poleOrderNat f s
    set G := meromorphicFactor f s hf h_neg.ne_top
    have hG_spec := ((meromorphicOrderAt_ne_top_iff hf).mp h_neg.ne_top).choose_spec
    have hG_an : AnalyticAt ℂ G s := hG_spec.1
    have hf_ev : f =ᶠ[𝓝[≠] s] fun z =>
        (z - s) ^ (meromorphicOrderAt f s).untop₀ • G z := hG_spec.2.2
    have hN_pos : 0 < N := poleOrderNat_pos_of_neg_order f s h_neg
    have h_ord_neg : (meromorphicOrderAt f s).untop₀ < 0 := by
      cases h : meromorphicOrderAt f s with
      | top => exact absurd h h_neg.ne_top
      | coe v => simp only [WithTop.untop₀_coe]; rw [h] at h_neg; exact_mod_cast h_neg
    have h_ord_eq : (meromorphicOrderAt f s).untop₀ = -(N : ℤ) := by
      change (meromorphicOrderAt f s).untop₀ = -↑((-((meromorphicOrderAt f s).untop₀)).toNat)
      omega
    set P : ℂ → ℂ := fun z => ∑ k ∈ Finset.range N,
      (iteratedDeriv k G s / ↑(k.factorial)) * (z - s) ^ (k : ℕ)
    have hP_an : AnalyticAt ℂ P s := by
      apply Finset.analyticAt_fun_sum; intro k _
      exact analyticAt_const.mul ((by fun_prop : AnalyticAt ℂ (· - s) s).pow _)
    have h_pp_eq : ∀ᶠ z in 𝓝[≠] s, meromorphicPrincipalPart f s z =
        (z - s) ^ (-(N : ℤ)) * P z := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hne : z - s ≠ 0 := sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hz)
      change meromorphicPrincipalPart f s z = _
      unfold meromorphicPrincipalPart; rw [dif_pos ⟨hf, h_neg⟩]
      simp only [P, N, G]; rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k _
      rw [show (z - s) ^ ((k : ℤ) - (poleOrderNat f s : ℤ)) =
        (z - s) ^ (-(poleOrderNat f s : ℤ)) * (z - s) ^ (k : ℕ) from by
        rw [← zpow_natCast (z - s) k, ← zpow_add₀ hne]; congr 1; omega]
      ring
    have h_taylor : ∃ H : ℂ → ℂ, AnalyticAt ℂ H s ∧
        ∀ᶠ z in 𝓝 s, G z - P z = (z - s) ^ N • H z :=
      taylor_remainder_factored G s N hG_an P rfl hP_an
    obtain ⟨H, hH_an, hH_eq⟩ := h_taylor
    refine ⟨H, hH_an, ?_⟩
    filter_upwards [hf_ev, h_pp_eq, hH_eq.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with z hf_z hpp_z hH_z hz_ne
    have hne : z - s ≠ 0 := sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hz_ne)
    simp only [smul_eq_mul] at hf_z hH_z ⊢
    rw [hf_z, hpp_z]; simp only [h_ord_eq]
    rw [← mul_sub, hH_z]
    rw [← mul_assoc, ← zpow_natCast (z - s) N, ← zpow_add₀ hne, neg_add_cancel,
      zpow_zero, one_mul]
  · have h_pp : meromorphicPrincipalPart f s = fun _ => 0 := by
      unfold meromorphicPrincipalPart
      rw [dif_neg (not_and_of_not_right _ h_neg)]
    push Not at h_neg
    refine ⟨toMeromorphicNFAt f s, ?_, ?_⟩
    · exact (meromorphicNFAt_toMeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt).mp
        (by rwa [← meromorphicOrderAt_congr hf.eq_nhdsNE_toMeromorphicNFAt])
    · filter_upwards [hf.eq_nhdsNE_toMeromorphicNFAt] with z hz
      simp [h_pp, hz]

/-! ### Local reproductions of zpow FTC lemmas

These lemmas were previously imported from FlatnessTransfer.lean. They are
reproved here locally to avoid a circular dependency. -/

/-- ContinuousOn for `t ↦ (γ(t) - s)^n` on a set where `γ(t) ≠ s`. -/
private theorem continuousOn_zpow_comp_sub'
    {γ : ℝ → ℂ} {s : ℂ} {n : ℤ} {A : Set ℝ}
    (hγ : ContinuousOn γ A)
    (hne : ∀ t ∈ A, γ t ≠ s) :
    ContinuousOn (fun t => (γ t - s) ^ n) A := by
  apply ContinuousOn.zpow₀ (hγ.sub continuousOn_const)
  intro t ht; exact Or.inl (sub_ne_zero.mpr (hne t ht))

/-- HasDerivAt for `(γ(t) - s)^n` when `γ` is differentiable and `γ(t) ≠ s`. -/
private theorem hasDerivAt_zpow_comp_sub'
    {γ : ℝ → ℂ} {s : ℂ} {n : ℤ} {t : ℝ} {L : ℂ}
    (hγ : HasDerivAt γ L t) (hne : γ t ≠ s) :
    HasDerivAt (fun t => (γ t - s) ^ n) (↑n * (γ t - s) ^ (n - 1) * L) t := by
  have h := (hasDerivAt_zpow n (γ t - s) (Or.inl (sub_ne_zero.mpr hne))).comp t (hγ.sub_const s)
  exact h.congr_deriv (by ring)

/-- FTC for the integral of `(γ(t) - s)^n * γ'(t)` on `[a, b]` when `γ(t) ≠ s`
on `[a, b]` and `n ≠ -1`. The primitive is `(γ(t) - s)^{n+1} / (n+1)`. -/
private theorem integral_zpow_comp_sub_mul_deriv'
    {γ : ℝ → ℂ} {s : ℂ} {n : ℤ} (hn : n ≠ -1)
    {a b : ℝ} (hab : a ≤ b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_ne : ∀ t ∈ Icc a b, γ t ≠ s)
    (E : Set ℝ) (hE : E.Countable) (_hE_sub : E ∩ Ioo a b ⊆ Ioo a b)
    (hγ_diff : ∀ t ∈ Ioo a b, t ∉ E → DifferentiableAt ℝ γ t)
    (h_int : IntervalIntegrable
      (fun t => (γ t - s) ^ n * (deriv γ t : ℂ)) MeasureTheory.volume a b) :
    ∫ t in a..b, (γ t - s) ^ n * (deriv γ t : ℂ) =
      ((γ b - s) ^ (n + 1) - (γ a - s) ^ (n + 1)) / (↑(n + 1) : ℂ) := by
  have hn1 : (n : ℤ) + 1 ≠ 0 := by omega
  have hn1_cast : (↑(n + 1) : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn1
  set F : ℝ → ℂ := fun t => (γ t - s) ^ (n + 1) / (↑(n + 1) : ℂ) with hF_def
  set f : ℝ → ℂ := fun t => (γ t - s) ^ n * (deriv γ t : ℂ) with hf_def
  have hF_cont : ContinuousOn F (Icc a b) :=
    (continuousOn_zpow_comp_sub' hγ_cont hγ_ne (n := n + 1)).div_const _
  have hE_count : (E ∩ Ioo a b).Countable := hE.mono Set.inter_subset_left
  have hF_deriv : ∀ t ∈ Ioo a b \ (E ∩ Ioo a b),
      HasDerivAt F (f t) t := by
    intro t ⟨ht, ht_not⟩
    have ht_not_E : t ∉ E := fun hE_mem => ht_not ⟨hE_mem, ht⟩
    have hne : γ t ≠ s := hγ_ne t (Ioo_subset_Icc_self ht)
    have h_div := (hasDerivAt_zpow_comp_sub' (n := n + 1)
      (hγ_diff t ht ht_not_E).hasDerivAt hne).div_const (↑(n + 1) : ℂ)
    change HasDerivAt F ((γ t - s) ^ n * ↑(deriv γ t)) t
    have : (↑(n + 1) : ℂ) * (γ t - s) ^ (n + 1 - 1) * ↑(deriv γ t) / (↑(n + 1) : ℂ)
        = (γ t - s) ^ n * ↑(deriv γ t) := by
      rw [show (n + 1 : ℤ) - 1 = n from by ring]
      rw [mul_assoc, mul_div_cancel_left₀ _ hn1_cast]
    rwa [this] at h_div
  rw [MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
    F f hab hE_count hF_cont hF_deriv h_int]
  simp only [F]
  rw [← sub_div]

/-! ### Contour integral of zpow on closed curves

For n <= -2, the function z |-> (z - s)^n has a primitive (z - s)^{n+1}/(n+1),
which is single-valued away from s. On a closed curve avoiding s, the boundary
terms cancel. -/

/-- For `n <= -2`, the contour integral `∮ (z - s)^n dz = 0` along any closed
piecewise C^1 immersion that avoids `s`. This follows from the fundamental
theorem of calculus: the primitive `(z-s)^{n+1}/(n+1)` is well-defined since
`n + 1 <= -1 != -1` (i.e. `n + 1 != 0`), and the boundary values cancel by closedness. -/
theorem contourIntegral_zpow_eq_zero (s : ℂ) (n : ℤ) (hn : n ≤ -2)
    (γ : PiecewiseC1Immersion) (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_avoids : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) :
    ∫ t in γ.a..γ.b, (γ.toFun t - s) ^ n * deriv γ.toFun t = 0 := by
  have hn_ne : n ≠ -1 := by omega
  have h_int : IntervalIntegrable
      (fun t => (γ.toFun t - s) ^ n * (deriv γ.toFun t : ℂ)) volume γ.a γ.b := by
    have h_zpow_cont : ContinuousOn (fun t => (γ.toFun t - s) ^ n) (Icc γ.a γ.b) :=
      continuousOn_zpow_comp_sub' γ.continuous_toFun hγ_avoids
    exact IntervalIntegrable.continuousOn_mul
      (piecewiseC1_deriv_intervalIntegrable γ.toPiecewiseC1Curve
        (piecewiseC1Immersion_deriv_bounded γ))
      (h_zpow_cont.mono (by rw [Set.uIcc_of_le (le_of_lt γ.hab)]))
  rw [integral_zpow_comp_sub_mul_deriv' hn_ne (le_of_lt γ.hab)
    γ.continuous_toFun hγ_avoids
    (↑γ.partition : Set ℝ) (γ.partition.finite_toSet.countable)
    (fun _ ⟨_, h⟩ => h)
    (fun t ht hn_part => γ.smooth_off_partition t (Ioo_subset_Icc_self ht) hn_part)
    h_int]
  rw [hγ_closed.symm, sub_self, zero_div]

/-- Variant: contour integral of `c * (z - s)^n` is zero for `n <= -2`. -/
theorem contourIntegral_const_mul_zpow_eq_zero (s : ℂ) (n : ℤ) (hn : n ≤ -2) (c : ℂ)
    (γ : PiecewiseC1Immersion) (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_avoids : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) :
    ∫ t in γ.a..γ.b, c * (γ.toFun t - s) ^ n * deriv γ.toFun t = 0 := by
  simp_rw [show ∀ t, c * (γ.toFun t - s) ^ n * deriv γ.toFun t =
      c * ((γ.toFun t - s) ^ n * deriv γ.toFun t) from fun t => by ring]
  erw [intervalIntegral.integral_const_mul,
    contourIntegral_zpow_eq_zero s n hn γ hγ_closed hγ_avoids]
  simp only [mul_zero]

/-! ### Residue of the principal part

The residue of the principal part equals the (N-1)-th coefficient `c_{N-1}`.
This is computed directly via circle integrals: in the sum `Σ c_k (z-s)^{k-N}`,
only the k=N-1 term (exponent -1) contributes to the residue. -/

/-- The residue of `Σ_{k<N} c_k * (z-s)^{k-N}` equals `c_{N-1}` (the coefficient
of `(z-s)^{-1}`). Proved directly by circle integral computation. -/
private theorem residueAt_zpow_sum (s : ℂ) (N : ℕ) (hN : 0 < N) (c : ℕ → ℂ) :
    residueAt (fun z => ∑ k ∈ Finset.range N, c k * (z - s) ^ ((k : ℤ) - (N : ℤ))) s =
    c (N - 1) := by
  unfold residueAt
  apply Filter.Tendsto.limUnder_eq
  apply tendsto_nhds_of_eventually_eq
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 from one_pos)] with r _ hr_pos
  simp only [Set.mem_Ioi] at hr_pos
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  have h2piI_ne : (2 : ℂ) * ↑Real.pi * I ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have h_term_integral : ∀ k, (∮ z in C(s, r),
      c k * (z - s) ^ ((k : ℤ) - (N : ℤ))) =
      if k = N - 1 then c (N - 1) * (2 * ↑Real.pi * I) else 0 := by
    intro k
    by_cases hk : k = N - 1
    · subst hk; simp only [↓reduceIte]
      have h_exp : ((N - 1 : ℕ) : ℤ) - (N : ℤ) = -1 := by omega
      have h_fn_eq : (fun z => c (N - 1) * (z - s) ^ (((N - 1 : ℕ) : ℤ) - (N : ℤ))) =
          fun z => c (N - 1) * (z - s)⁻¹ := by ext z; rw [h_exp, zpow_neg_one]
      conv_lhs => rw [h_fn_eq]
      rw [circleIntegral.integral_const_mul, circleIntegral.integral_sub_center_inv s hr_ne]
    · simp only [hk, ↓reduceIte]
      conv_lhs => rw [show (fun z => c k * (z - s) ^ ((k : ℤ) - (N : ℤ))) =
        fun z => c k * (z - s) ^ ((k : ℤ) - (N : ℤ)) from rfl]
      rw [circleIntegral.integral_const_mul,
        circleIntegral.integral_sub_zpow_of_ne (show (k : ℤ) - (N : ℤ) ≠ -1 by omega),
        mul_zero]
  have h_sum_eq : (∮ z in C(s, r),
      ∑ k ∈ Finset.range N, c k * (z - s) ^ ((k : ℤ) - (N : ℤ))) =
      ∑ k ∈ Finset.range N,
        (∮ z in C(s, r), c k * (z - s) ^ ((k : ℤ) - (N : ℤ))) := by
    have h_ci : ∀ k, CircleIntegrable (fun z => c k * (z - s) ^ ((k : ℤ) - (N : ℤ))) s r := by
      intro k
      have h_zpow_ci : CircleIntegrable (fun z => (z - s) ^ ((k : ℤ) - (N : ℤ))) s r :=
        circleIntegrable_sub_zpow_iff.mpr (Or.inr (Or.inr (by
          intro hmem
          rw [Metric.mem_sphere] at hmem
          simp [dist_self] at hmem
          exact hr_ne (abs_eq_zero.mp hmem.symm))))
      exact h_zpow_ci.const_fun_smul
    have : ∀ S : Finset ℕ,
        (∮ z in C(s, r), ∑ k ∈ S, c k * (z - s) ^ ((k : ℤ) - (N : ℤ))) =
        ∑ k ∈ S, (∮ z in C(s, r), c k * (z - s) ^ ((k : ℤ) - (N : ℤ))) := by
      intro S; induction S using Finset.induction with
      | empty => simp [circleIntegral]
      | @insert a S' ha' ih =>
        simp_rw [Finset.sum_insert ha']
        have h_sum_ci : CircleIntegrable
            (fun z => ∑ k ∈ S', c k * (z - s) ^ ((k : ℤ) - (N : ℤ))) s r := by
          have := CircleIntegrable.sum S'
            (f := fun k => fun z => c k * (z - s) ^ ((k : ℤ) - (N : ℤ)))
            (fun k _ => h_ci k)
          rwa [show (∑ k ∈ S', (fun z => c k * (z - s) ^ ((k : ℤ) - (N : ℤ)))) =
            fun z => ∑ k ∈ S', c k * (z - s) ^ ((k : ℤ) - (N : ℤ)) from
            funext (fun z => Finset.sum_apply z S' _)] at this
        rw [circleIntegral.integral_add (h_ci a) h_sum_ci, ih]
    exact this _
  rw [h_sum_eq]
  simp_rw [h_term_integral]
  rw [Finset.sum_ite_eq' (Finset.range N) (N - 1)]
  simp only [Finset.mem_range, Nat.sub_one_lt_of_le hN le_rfl, ↓reduceIte]
  rw [mul_comm (c (N - 1)) _, ← mul_assoc, inv_mul_cancel₀ h2piI_ne, one_mul]

/-! ### Principal part integral vanishing

When the residue is zero, the principal part integral vanishes on closed curves.
The principal part is a finite sum of terms `c_k * (z - s)^{k - N}` for k = 0..N-1.
The term with k = N-1 gives exponent -1 (the residue term), which vanishes by assumption.
All other terms have exponent <= -2, so they vanish by `contourIntegral_zpow_eq_zero`. -/

/-- The residue of `f` equals the residue of its principal part sum. Since `f - pp` is
analytic near `s`, the circle integrals of `f` and `pp` agree for small radius, so
the residues (defined as limits of circle integrals) are equal. -/
private theorem residueAt_eq_residueAt_principalPart_sum (f : ℂ → ℂ) (s : ℂ)
    (hf : MeromorphicAt f s) (N : ℕ) (g : ℂ → ℂ)
    (h_pp_eq : meromorphicPrincipalPart f s = fun z =>
        (Finset.range N).sum fun k =>
          (iteratedDeriv k g s / ↑(Nat.factorial k)) * (z - s) ^ ((k : ℤ) - (N : ℤ))) :
    residueAt f s = residueAt (fun z =>
        ∑ k ∈ Finset.range N,
          iteratedDeriv k g s / ↑(k.factorial) * (z - s) ^ ((k : ℤ) - (N : ℤ))) s := by
  set pp := fun z => ∑ k ∈ Finset.range N,
    iteratedDeriv k g s / ↑(k.factorial) * (z - s) ^ ((k : ℤ) - (N : ℤ))
  have h_pp_is : pp = meromorphicPrincipalPart f s := by
    ext z; rw [h_pp_eq]
  obtain ⟨g_an, hg_an_at, hg_eq⟩ :=
    meromorphicAt_sub_principalPart_eventually f s hf
  have hg_eq' : ∀ᶠ z in 𝓝[≠] s, f z - pp z = g_an z := by
    rw [h_pp_is]; exact hg_eq
  obtain ⟨rg, hrg_pos, hg_ball⟩ := hg_an_at.exists_ball_analyticOnNhd
  rw [Filter.Eventually, Metric.mem_nhdsWithin_iff] at hg_eq'
  obtain ⟨rf, hrf_pos, hrf_eq⟩ := hg_eq'
  have hr₀_pos : 0 < min rg rf := lt_min hrg_pos hrf_pos
  unfold residueAt
  apply limUnder_eventually_eq
  apply Filter.Eventually.mono (Ioo_mem_nhdsGT hr₀_pos)
  intro r ⟨hr_pos, hr_lt⟩
  have hr_lt_rg : r < rg := lt_of_lt_of_le hr_lt (min_le_left _ _)
  have hr_lt_rf : r < rf := lt_of_lt_of_le hr_lt (min_le_right _ _)
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  suffices h_circ : (∮ z in C(s, r), f z) = (∮ z in C(s, r), pp z) by
    rw [h_circ]
  have h_eq_on : Set.EqOn f (fun z => pp z + g_an z) (Metric.sphere s r) := by
    intro z hz
    have h_ne : z ≠ s := by
      intro heq; rw [heq, Metric.mem_sphere, dist_self] at hz; linarith
    have h_in : dist z s < rf := by
      rw [Metric.mem_sphere.mp hz]; exact hr_lt_rf
    have h_mem : z ∈ Metric.ball s rf ∩ {s}ᶜ :=
      ⟨Metric.mem_ball.mpr h_in, Set.mem_compl_singleton_iff.mpr h_ne⟩
    rw [show f z = pp z + (f z - pp z) from (add_sub_cancel _ _).symm,
      show f z - pp z = g_an z from by simpa using hrf_eq h_mem]
  have h_g_cont : ContinuousOn g_an (Metric.closedBall s r) :=
    hg_ball.continuousOn.mono (Metric.closedBall_subset_ball hr_lt_rg)
  have h_ci_g : CircleIntegrable g_an s r :=
    (h_g_cont.mono Metric.sphere_subset_closedBall).circleIntegrable hr_pos.le
  have hs_not : s ∉ Metric.sphere s r := by simp [hr_ne.symm]
  have h_pp_cont : ContinuousOn pp (Metric.sphere s r) := by
    apply continuousOn_finsetSum
    intro k _
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.zpow₀ (continuousOn_id.sub continuousOn_const)
    intro z hz
    exact Or.inl (sub_ne_zero.mpr (ne_of_mem_of_not_mem hz hs_not))
  have h_ci_pp : CircleIntegrable pp s r :=
    h_pp_cont.circleIntegrable hr_pos.le
  rw [circleIntegral.integral_congr hr_pos.le h_eq_on,
    circleIntegral.integral_add h_ci_pp h_ci_g]
  have h_g_zero : (∮ z in C(s, r), g_an z) = 0 :=
    circleIntegral_eq_zero_of_differentiable_on_off_countable hr_pos.le
      Set.countable_empty h_g_cont
      (fun z ⟨hz, _⟩ => (hg_ball z (Metric.ball_subset_ball hr_lt_rg.le hz)).differentiableAt)
  rw [h_g_zero, add_zero]

/-- The contour integral of the principal part vanishes when the residue is zero. -/
theorem contourIntegral_principalPart_eq_zero_of_residue_zero
    (f : ℂ → ℂ) (s : ℂ) (hf : MeromorphicAt f s)
    (hres : residueAt f s = 0)
    (γ : PiecewiseC1Immersion) (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_avoids : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) :
    ∫ t in γ.a..γ.b, meromorphicPrincipalPart f s (γ.toFun t) * deriv γ.toFun t = 0 := by
  by_cases h_neg : meromorphicOrderAt f s < 0
  · set N := poleOrderNat f s with hN_def
    set g := meromorphicFactor f s hf h_neg.ne_top with hg_def
    have hN_pos : 0 < N := poleOrderNat_pos_of_neg_order f s h_neg
    have h_pp_eq : meromorphicPrincipalPart f s = fun z =>
        (Finset.range N).sum fun k =>
          (iteratedDeriv k g s / ↑(Nat.factorial k)) * (z - s) ^ ((k : ℤ) - (N : ℤ)) := by
      unfold meromorphicPrincipalPart
      rw [dif_pos ⟨hf, h_neg⟩]
    rw [h_pp_eq]
    simp_rw [Finset.sum_mul]
    have h_coeff_zero : iteratedDeriv (N - 1) g s / ↑((N - 1).factorial) = 0 := by
      have h_res_eq : residueAt f s = residueAt (fun z =>
          ∑ k ∈ Finset.range N,
            iteratedDeriv k g s / ↑(k.factorial) * (z - s) ^ ((k : ℤ) - (N : ℤ))) s :=
        residueAt_eq_residueAt_principalPart_sum f s hf N g h_pp_eq
      rw [hres] at h_res_eq
      rw [← residueAt_zpow_sum s N hN_pos (fun k => iteratedDeriv k g s / ↑(k.factorial))]
      exact h_res_eq.symm
    have h_int : ∀ k ∈ Finset.range N, IntervalIntegrable
        (fun t => iteratedDeriv k g s / ↑(k.factorial) * (γ.toFun t - s) ^
          ((k : ℤ) - (N : ℤ)) * deriv γ.toFun t) MeasureTheory.volume γ.a γ.b := by
      intro k _
      have h_zpow_cont : ContinuousOn
          (fun t => (γ.toFun t - s) ^ ((k : ℤ) - (N : ℤ))) (Icc γ.a γ.b) :=
        continuousOn_zpow_comp_sub' γ.continuous_toFun hγ_avoids
      have h_const_zpow_cont : ContinuousOn
          (fun t => iteratedDeriv k g s / ↑(k.factorial) *
            (γ.toFun t - s) ^ ((k : ℤ) - (N : ℤ))) (Icc γ.a γ.b) :=
        (continuousOn_const.mul h_zpow_cont)
      exact IntervalIntegrable.continuousOn_mul
        (piecewiseC1_deriv_intervalIntegrable γ.toPiecewiseC1Curve
          (piecewiseC1Immersion_deriv_bounded γ))
        (h_const_zpow_cont.mono (by rw [Set.uIcc_of_le (le_of_lt γ.hab)]))
    rw [intervalIntegral.integral_finsetSum h_int]
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_range] at hk
    by_cases hk_eq : k = N - 1
    · subst hk_eq
      simp only [h_coeff_zero, zero_mul, intervalIntegral.integral_zero]
    · have hk_lt : k < N - 1 := by omega
      have h_exp : (k : ℤ) - (N : ℤ) ≤ -2 := by omega
      exact contourIntegral_const_mul_zpow_eq_zero s _ h_exp _ γ hγ_closed hγ_avoids
  · have h_pp : meromorphicPrincipalPart f s = fun _ => 0 := by
      unfold meromorphicPrincipalPart
      rw [dif_neg (not_and_of_not_right _ h_neg)]
    simp only [h_pp, zero_mul, intervalIntegral.integral_zero]

end GeneralizedResidueTheory

end
