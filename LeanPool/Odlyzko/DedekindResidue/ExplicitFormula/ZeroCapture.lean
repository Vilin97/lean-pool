/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib
public import LeanPool.Odlyzko.DedekindResidue.ExplicitFormula.RectangleContour
public import LeanPool.Odlyzko.DedekindResidue.CompletedZeta.AnalyticControl
public import LeanPool.Odlyzko.CebotarevDensity.NumberFieldEulerProduct

/-!
# Zero capture on the explicit-formula rectangle  (SP2-RECT R-a)

The residue side of Poitou's contour identity needs `H = completedDedekindZetaEntire`
peeled into (divisor product)·(zero-free analytic) on an open **rectangle** — the
rectangle version of the ball peeling from SP1-AC. The nonvanishing witness is the
real ray: `H(x) ≠ 0` for real `x > 1`, by the Euler-product positivity
`Chebotarev.dedekindZeta_re_pos_of_one_lt` (first cross-project reuse) together with
the nonvanishing of `s(s−1)`, `|Δ|^{s/2}` and the archimedean factor.

Route: `.mathlib-quality/decomposition-sp2.md`, leaf SP2-RECT R-a.
-/

@[expose] public section

namespace DedekindResidue

open MeasureTheory Complex NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- `H = completedDedekindZetaEntire K` is analytic at every point (it is entire).
The single reusable analyticity fact behind the divisor, zero-order and
meromorphicity arguments for `H` throughout this file. -/
theorem analyticAt_completedDedekindZetaEntire (ζ : ℂ) :
    AnalyticAt ℂ (completedDedekindZetaEntire K) ζ :=
  (differentiable_completedDedekindZetaEntire K).analyticAt ζ

/-- Open rectangles are convex: they are intersections of linear preimages of
intervals under `re` and `im`. -/
theorem convex_reProdIm {s t : Set ℝ} (hs : Convex ℝ s) (ht : Convex ℝ t) :
    Convex ℝ (s ×ℂ t) :=
  (hs.linear_preimage Complex.reLm).inter (ht.linear_preimage Complex.imLm)

/-- Open rectangles are bounded. -/
theorem isBounded_Ioo_reProdIm (a b c d : ℝ) :
    Bornology.IsBounded (Set.Ioo a b ×ℂ Set.Ioo c d) :=
  (Metric.isBounded_Ioo a b).reProdIm (Metric.isBounded_Ioo c d)

/-- **Rectangle zero-peeling** (SP2-RECT R-a): on an open rectangle where `H` is not
identically zero, `H` factors as the divisor product times a zero-free analytic
function — the rectangle version of `exists_H_ball_factorization`. -/
theorem exists_H_rectangle_factorization {a b c d : ℝ}
    {w : ℂ} (hw : w ∈ Set.Ioo a b ×ℂ Set.Ioo c d)
    (hHw : completedDedekindZetaEntire K w ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (Set.Ioo a b ×ℂ Set.Ioo c d)
      ∧ (∀ z ∈ Set.Ioo a b ×ℂ Set.Ioo c d, g z ≠ 0)
      ∧ ∀ z ∈ Set.Ioo a b ×ℂ Set.Ioo c d,
          completedDedekindZetaEntire K z
            = (∏ᶠ u, (z - u) ^ ((MeromorphicOn.divisor (completedDedekindZetaEntire K)
                (Set.Ioo a b ×ℂ Set.Ioo c d)) u)) * g z := by
  set U : Set ℂ := Set.Ioo a b ×ℂ Set.Ioo c d with hU
  have hUo : IsOpen U := (isOpen_Ioo).reProdIm (isOpen_Ioo)
  have hUc : Convex ℝ U := convex_reProdIm (convex_Ioo a b) (convex_Ioo c d)
  have hHmero : MeromorphicOn (completedDedekindZetaEntire K) U := fun z _ =>
    (analyticAt_completedDedekindZetaEntire K z).meromorphicAt
  have hordw : meromorphicOrderAt (completedDedekindZetaEntire K) w ≠ ⊤ := by
    rw [(analyticAt_completedDedekindZetaEntire K w).meromorphicOrderAt_eq]
    have h0 : analyticOrderAt (completedDedekindZetaEntire K) w = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr hHw)
    rw [h0]
    simp
  have hord : ∀ u : U, meromorphicOrderAt (completedDedekindZetaEntire K) u ≠ ⊤ := by
    intro u
    exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected hHmero
      hUc.isPreconnected hw u.2 hordw
  -- the rectangle sits in a compact closed ball, so the divisor support is finite
  obtain ⟨R₀, hR₀⟩ := (isBounded_Ioo_reProdIm a b c d).subset_closedBall (0 : ℂ)
  have hfin : ((MeromorphicOn.divisor (completedDedekindZetaEntire K) U)).support.Finite :=
    MeromorphicOn.divisor_support_finite_of_subset
      (fun z _ => (analyticAt_completedDedekindZetaEntire K z).meromorphicAt)
      (isCompact_closedBall (0:ℂ) R₀) hR₀
  obtain ⟨g, hganal, hgne, heq⟩ :=
    MeromorphicOn.extract_zeros_poles hHmero hord hfin
  have hfinsupp : Function.HasFiniteSupport
      ((MeromorphicOn.divisor (completedDedekindZetaEntire K) U) : ℂ → ℤ) := hfin
  have hdivpos : ∀ u : ℂ,
      0 ≤ (MeromorphicOn.divisor (completedDedekindZetaEntire K) U) u := by
    intro u
    exact (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (fun z _ =>
      analyticAt_completedDedekindZetaEntire K z)) u
  have hprodanal : ∀ z : ℂ, AnalyticAt ℂ
      (∏ᶠ u, (· - u) ^ ((MeromorphicOn.divisor (completedDedekindZetaEntire K) U) u)) z :=
    fun z => Function.FactorizedRational.analyticAt (hdivpos z)
  have heqOn : Set.EqOn (completedDedekindZetaEntire K)
      ((∏ᶠ u, (· - u) ^ ((MeromorphicOn.divisor (completedDedekindZetaEntire K) U) u))
        • g) U := by
    refine eqOn_of_eventuallyEq_codiscreteWithin hUo heq
      (differentiable_completedDedekindZetaEntire K).continuous.continuousOn ?_
    simpa only [smul_eq_mul] using ContinuousOn.mul
      (fun z _ => (hprodanal z).continuousAt.continuousWithinAt) hganal.continuousOn
  refine ⟨g, hganal, fun z hz => hgne ⟨z, hz⟩, fun z hz => ?_⟩
  have := heqOn hz
  rw [this, Pi.smul_apply', smul_eq_mul]
  congr 1
  rw [Function.FactorizedRational.finprod_eq_fun hfinsupp]

/-- **The rectangle argument principle for `H`** (SP2-RECT R-d): if `H` has no zeros
on the boundary of the rectangle and `Φ` is holomorphic at every point of the closed
rectangle, then `∮_{∂R} Φ·H'/H = 2πi·∑_ρ m_ρ·Φ(ρ)`, summed over the divisor of `H`
on the open rectangle. -/
theorem rectangleIntegral_mul_logDeriv_H {z w : ℂ} (hre : z.re < w.re) (him : z.im < w.im)
    {Φ : ℂ → ℂ}
    (hΦ : ∀ ζ ∈ Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im, DifferentiableAt ℂ Φ ζ)
    (hbound : ∀ ζ ∈ rectangleBoundary z w, completedDedekindZetaEntire K ζ ≠ 0)
    {w₀ : ℂ} (hw₀ : w₀ ∈ Set.Ioo (z.re - 1) (w.re + 1) ×ℂ Set.Ioo (z.im - 1) (w.im + 1))
    (hHw₀ : completedDedekindZetaEntire K w₀ ≠ 0) :
    rectangleIntegral (fun ζ => Φ ζ * logDeriv (completedDedekindZetaEntire K) ζ) z w
      = 2 * Real.pi * Complex.I
        * ∑ᶠ ρ, (((MeromorphicOn.divisor (completedDedekindZetaEntire K)
            (Set.Ioo z.re w.re ×ℂ Set.Ioo z.im w.im)) ρ : ℂ)) * Φ ρ := by
  classical
  set U' : Set ℂ := Set.Ioo (z.re - 1) (w.re + 1) ×ℂ Set.Ioo (z.im - 1) (w.im + 1) with hU'
  have hU'o : IsOpen U' := isOpen_Ioo.reProdIm isOpen_Ioo
  set V : Set ℂ := Set.Ioo z.re w.re ×ℂ Set.Ioo z.im w.im with hV
  set Rc : Set ℂ := Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im with hRc
  -- inclusions
  have hRcU' : Rc ⊆ U' := by
    intro ζ hζ
    rw [hRc, Complex.mem_reProdIm,
      Set.uIcc_of_le hre.le, Set.uIcc_of_le him.le] at hζ
    rw [hU', Complex.mem_reProdIm]
    obtain ⟨h1, h2⟩ := hζ
    rw [Set.mem_Icc] at h1 h2
    constructor <;> rw [Set.mem_Ioo] <;> constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hbdRc : rectangleBoundary z w ⊆ Rc := by
    intro ζ hζ
    rw [rectangleBoundary] at hζ
    rw [hRc, Complex.mem_reProdIm]
    rcases hζ with hζ | hζ <;> rw [Complex.mem_reProdIm] at hζ
    · refine ⟨hζ.1, ?_⟩
      rcases hζ.2 with h | h <;> rw [h]
      · exact Set.left_mem_uIcc
      · exact Set.right_mem_uIcc
    · refine ⟨?_, hζ.2⟩
      rcases hζ.1 with h | h <;> rw [h]
      · exact Set.left_mem_uIcc
      · exact Set.right_mem_uIcc
  have hVU' : V ⊆ U' := by
    intro ζ hζ
    rw [hV, Complex.mem_reProdIm] at hζ
    rw [hU', Complex.mem_reProdIm]
    obtain ⟨h1, h2⟩ := hζ
    rw [Set.mem_Ioo] at h1 h2
    constructor <;> rw [Set.mem_Ioo] <;> constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  -- closed-minus-open is the boundary
  have hsplit_closed : ∀ v ∈ Rc, v ∈ V ∨ v ∈ rectangleBoundary z w := by
    intro v hv
    rw [hRc, Complex.mem_reProdIm, Set.uIcc_of_le hre.le, Set.uIcc_of_le him.le] at hv
    obtain ⟨h1, h2⟩ := hv
    rw [Set.mem_Icc] at h1 h2
    by_cases hin : v ∈ V
    · exact Or.inl hin
    · refine Or.inr ?_
      rw [hV, Complex.mem_reProdIm, Set.mem_Ioo, Set.mem_Ioo] at hin
      push Not at hin
      rw [rectangleBoundary]
      by_cases hres : v.re = z.re ∨ v.re = w.re
      · refine Set.mem_union_right _ ?_
        rw [Complex.mem_reProdIm]
        refine ⟨hres, ?_⟩
        rw [Set.uIcc_of_le him.le, Set.mem_Icc]
        exact h2
      · push Not at hres
        refine Set.mem_union_left _ ?_
        rw [Complex.mem_reProdIm]
        constructor
        · rw [Set.uIcc_of_le hre.le, Set.mem_Icc]
          exact h1
        · have hre1 : z.re < v.re := lt_of_le_of_ne h1.1 (Ne.symm hres.1)
          have hre2 : v.re < w.re := lt_of_le_of_ne h1.2 hres.2
          have himp := hin ⟨hre1, hre2⟩
          rcases eq_or_lt_of_le h2.1 with h | h
          · exact Or.inl h.symm
          · rcases eq_or_lt_of_le h2.2 with h' | h'
            · exact Or.inr h'
            · exact absurd (himp h) (not_le.mpr h')
  -- peel H on the enlarged rectangle
  obtain ⟨g, hganal, hgne, hfac⟩ := exists_H_rectangle_factorization K hw₀ hHw₀
  set D : ℂ → ℤ := fun u => (MeromorphicOn.divisor (completedDedekindZetaEntire K) U') u
    with hD
  have hHanal : ∀ ζ : ℂ, AnalyticAt ℂ (completedDedekindZetaEntire K) ζ :=
    analyticAt_completedDedekindZetaEntire K
  have hDnn : ∀ u, 0 ≤ D u := fun u =>
    (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (fun ζ _ => hHanal ζ)) u
  obtain ⟨R₀, hR₀⟩ := (isBounded_Ioo_reProdIm (z.re - 1) (w.re + 1) (z.im - 1)
    (w.im + 1)).subset_closedBall (0 : ℂ)
  have hfin : (Function.support D).Finite :=
    MeromorphicOn.divisor_support_finite_of_subset
      (fun ζ _ => (hHanal ζ).meromorphicAt) (isCompact_closedBall (0:ℂ) R₀) hR₀
  set F : Finset ℂ := hfin.toFinset with hF
  have hP₁ : ∀ ζ : ℂ, (∏ᶠ u, (ζ - u) ^ D u) = ∏ u ∈ F, (ζ - u) ^ D u := by
    intro ζ
    refine finprod_eq_prod_of_mulSupport_subset _ ?_
    intro u hu
    rw [Function.mem_mulSupport] at hu
    refine hfin.mem_toFinset.mpr (Function.mem_support.mpr ?_)
    intro h0
    rw [h0, zpow_zero] at hu
    exact hu rfl
  have hfacF : ∀ ζ ∈ U', completedDedekindZetaEntire K ζ
      = (∏ u ∈ F, (ζ - u) ^ D u) * g ζ := by
    intro ζ hζ
    rw [hfac ζ hζ, hP₁ ζ]
  -- points of F are zeros of H
  have hFzero : ∀ u ∈ F, completedDedekindZetaEntire K u = 0 := by
    intro u hu
    by_contra hne0
    have hord0 : analyticOrderAt (completedDedekindZetaEntire K) u = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr hne0)
    have huU' : u ∈ U' := (MeromorphicOn.divisor (completedDedekindZetaEntire K)
      U').supportWithinDomain (hfin.mem_toFinset.mp hu)
    have hDu : D u = 0 := by
      rw [hD]
      simp only
      rw [MeromorphicOn.divisor_apply (fun ζ _ => (hHanal ζ).meromorphicAt) huU',
        (hHanal u).meromorphicOrderAt_eq, hord0]
      simp
    exact (Function.mem_support.mp (hfin.mem_toFinset.mp hu)) hDu
  -- boundary facts
  have hbdne : ∀ ζ ∈ rectangleBoundary z w, ∀ u ∈ F, ζ ≠ u := by
    intro ζ hζ u hu h0
    exact hbound ζ hζ (h0 ▸ hFzero u hu)
  have hbdg : ∀ ζ ∈ rectangleBoundary z w, g ζ ≠ 0 :=
    fun ζ hζ => hgne ζ (hRcU' (hbdRc hζ))
  -- pointwise boundary identity
  have hpt : Set.EqOn (fun ζ => Φ ζ * logDeriv (completedDedekindZetaEntire K) ζ)
      (fun ζ => (∑ u ∈ F, (D u : ℂ) * (Φ ζ * (ζ - u)⁻¹)) + Φ ζ * logDeriv g ζ)
      (rectangleBoundary z w) := by
    intro ζ hζ
    simp only
    rw [logDeriv_eq_sum_add_of_factorization hU'o hfacF hDnn hganal
      (hRcU' (hbdRc hζ)) (hbdg ζ hζ) (fun u hu => hbdne ζ hζ u hu)]
    rw [mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun u hu => ?_)
    ring
  -- continuity of the pieces on the boundary
  have hΦcont : ContinuousOn Φ (rectangleBoundary z w) :=
    fun ζ hζ => (hΦ ζ (hbdRc hζ)).continuousAt.continuousWithinAt
  have hsum_cont : ∀ u ∈ F, ContinuousOn
      (fun ζ => (D u : ℂ) * (Φ ζ * (ζ - u)⁻¹)) (rectangleBoundary z w) := by
    intro u hu
    refine ContinuousOn.mul continuousOn_const (ContinuousOn.mul hΦcont ?_)
    refine ContinuousOn.inv₀ (by fun_prop) ?_
    intro ζ hζ
    exact sub_ne_zero_of_ne (hbdne ζ hζ u hu)
  have hlast_cont : ContinuousOn (fun ζ => Φ ζ * logDeriv g ζ)
      (rectangleBoundary z w) := by
    refine ContinuousOn.mul hΦcont ?_
    have hld : (logDeriv g) = fun ζ => deriv g ζ / g ζ := rfl
    rw [hld]
    refine ContinuousOn.div ?_ ?_ ?_
    · intro ζ hζ
      exact ((hganal ζ (hRcU' (hbdRc hζ))).deriv.continuousAt).continuousWithinAt
    · intro ζ hζ
      exact ((hganal ζ (hRcU' (hbdRc hζ))).continuousAt).continuousWithinAt
    · intro ζ hζ
      exact hbdg ζ hζ
  -- split the boundary integral
  rw [rectangleIntegral_congr hpt]
  rw [rectangleIntegral_add (by
    refine continuousOn_finsetSum F (fun u hu => hsum_cont u hu)) hlast_cont]
  rw [rectangleIntegral_finset_sum F _ hsum_cont]
  -- more inclusions
  have hVRc : V ⊆ Rc := by
    intro ζ hζ
    rw [hV, Complex.mem_reProdIm] at hζ
    rw [hRc, Complex.mem_reProdIm, Set.uIcc_of_le hre.le, Set.uIcc_of_le him.le]
    exact ⟨Set.Ioo_subset_Icc_self hζ.1, Set.Ioo_subset_Icc_self hζ.2⟩
  have hminmax : Set.Ioo (min z.re w.re) (max z.re w.re) ×ℂ
      Set.Ioo (min z.im w.im) (max z.im w.im) = V := by
    rw [hV, min_eq_left hre.le, max_eq_right hre.le, min_eq_left him.le,
      max_eq_right him.le]
  -- the zero-free part integrates to zero (Goursat)
  have hΦcontRc : ContinuousOn Φ Rc :=
    fun ζ hζ => (hΦ ζ hζ).continuousAt.continuousWithinAt
  have hglast : rectangleIntegral (fun ζ => Φ ζ * logDeriv g ζ) z w = 0 := by
    refine rectangleIntegral_eq_zero Set.countable_empty ?_ ?_
    · refine ContinuousOn.mul hΦcontRc ?_
      have hld : (logDeriv g) = fun ζ => deriv g ζ / g ζ := rfl
      rw [hld]
      refine ContinuousOn.div ?_ ?_ ?_
      · exact fun ζ hζ => ((hganal ζ (hRcU' hζ)).deriv.continuousAt).continuousWithinAt
      · exact fun ζ hζ => ((hganal ζ (hRcU' hζ)).continuousAt).continuousWithinAt
      · exact fun ζ hζ => hgne ζ (hRcU' hζ)
    · intro x hx
      have hxV : x ∈ V := by
        rw [← hminmax]
        exact hx.1
      refine DifferentiableAt.mul (hΦ x (hVRc hxV)) ?_
      have hld : (logDeriv g) = fun ζ => deriv g ζ / g ζ := rfl
      rw [hld]
      refine DifferentiableAt.div ?_ ?_ ?_
      · exact ((hganal x (hVU' hxV)).deriv).differentiableAt
      · exact (hganal x (hVU' hxV)).differentiableAt
      · exact hgne x (hVU' hxV)
  rw [hglast, add_zero]
  -- evaluate each peeled term
  have heval : ∀ u ∈ F, rectangleIntegral (fun ζ => Φ ζ * (ζ - u)⁻¹) z w
      = if u ∈ V then 2 * Real.pi * Complex.I * Φ u else 0 := by
    intro u hu
    by_cases hin : u ∈ V
    · rw [if_pos hin]
      have hin' := hin
      rw [hV, Complex.mem_reProdIm, Set.mem_Ioo, Set.mem_Ioo] at hin'
      exact rectangleIntegral_cauchy hΦ hin'.1.1 hin'.1.2 hin'.2.1 hin'.2.2
    · rw [if_neg hin]
      have hunotRc : u ∉ Rc := by
        intro huRc
        rcases hsplit_closed u huRc with h | h
        · exact hin h
        · exact hbound u h (hFzero u hu)
      refine rectangleIntegral_eq_zero Set.countable_empty ?_ ?_
      · refine ContinuousOn.mul hΦcontRc ?_
        refine ContinuousOn.inv₀ (by fun_prop) ?_
        intro ζ hζ
        refine sub_ne_zero_of_ne ?_
        intro h0
        exact hunotRc (h0 ▸ hζ)
      · intro x hx
        have hxV : x ∈ V := by
          rw [← hminmax]
          exact hx.1
        refine DifferentiableAt.mul (hΦ x (hVRc hxV)) ?_
        refine DifferentiableAt.inv (differentiableAt_id.sub_const u) ?_
        refine sub_ne_zero_of_ne ?_
        intro h0
        exact hunotRc (h0 ▸ hVRc hxV)
  -- fold the sum into the divisor finsum
  have hDV : ∀ u ∈ V, (MeromorphicOn.divisor (completedDedekindZetaEntire K) V) u
      = D u := by
    intro u huV
    rw [hD]
    simp only
    rw [MeromorphicOn.divisor_apply (fun ζ _ => (hHanal ζ).meromorphicAt) huV,
      MeromorphicOn.divisor_apply (fun ζ _ => (hHanal ζ).meromorphicAt) (hVU' huV)]
  have hsupp : (Function.support
      (fun ρ => (((MeromorphicOn.divisor (completedDedekindZetaEntire K) V) ρ : ℂ)) * Φ ρ))
      ⊆ (F : Set ℂ) := by
    intro ρ hρ
    rw [Function.mem_support] at hρ
    have hdV : (MeromorphicOn.divisor (completedDedekindZetaEntire K) V) ρ ≠ 0 := by
      intro h0
      rw [h0] at hρ
      simp at hρ
    have hρV : ρ ∈ V := by
      by_contra hnot
      exact hdV (Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hnot)
    have : D ρ ≠ 0 := by
      rw [← hDV ρ hρV]
      exact hdV
    exact hfin.mem_toFinset.mpr (Function.mem_support.mpr this)
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun u hu => ?_)
  rw [rectangleIntegral_const_mul, heval u hu]
  by_cases hin : u ∈ V
  · rw [if_pos hin, hDV u hin]
    ring
  · rw [if_neg hin,
      Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hin]
    simp

/-- **Euler-product nonvanishing**: `ζ_K(s) ≠ 0` for `Re s > 1`. Each Euler factor is
`1 + f_𝔭` with `f_𝔭 = (1 − N𝔭^{-s})⁻¹ − 1` absolutely summable, so the product is a
nonzero limit (`tprod_one_add_ne_zero_of_summable`, the Dedekind-eta pattern). -/
theorem dedekindZeta_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta K s ≠ 0 := by
  rw [Chebotarev.dedekindZeta_eq_tprod_primeIdeal K hs]
  set x : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} → ℂ :=
    fun 𝔭 => (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s) with hx
  -- factor norms are at most 1/2
  have hnormeq : ∀ 𝔭, ‖x 𝔭‖ = (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s.re) := by
    intro 𝔭
    have hne0 : Ideal.absNorm 𝔭.1 ≠ 0 := fun h => 𝔭.2.2 (Ideal.absNorm_eq_zero_iff.mp h)
    rw [hx]
    simp only
    rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
  have hhalf : ∀ 𝔭, ‖x 𝔭‖ ≤ 1/2 := by
    intro 𝔭
    have hne0 : Ideal.absNorm 𝔭.1 ≠ 0 := fun h => 𝔭.2.2 (Ideal.absNorm_eq_zero_iff.mp h)
    have hne1 : Ideal.absNorm 𝔭.1 ≠ 1 := fun h => 𝔭.2.1.ne_top (Ideal.absNorm_eq_one_iff.mp h)
    have h2 : (2:ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) := by
      have : 2 ≤ Ideal.absNorm 𝔭.1 := by omega
      exact_mod_cast this
    rw [hnormeq 𝔭]
    have hstep1 : (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s.re) ≤ (2:ℝ) ^ (-s.re) := by
      rw [Real.rpow_neg (by linarith), Real.rpow_neg (by norm_num)]
      refine (inv_le_inv₀ (Real.rpow_pos_of_pos (by linarith) _)
        (Real.rpow_pos_of_pos (by norm_num) _)).mpr ?_
      exact Real.rpow_le_rpow (by norm_num) h2 (by linarith)
    have hstep2 : (2:ℝ) ^ (-s.re) ≤ (2:ℝ) ^ (-(1:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hstep3 : (2:ℝ) ^ (-(1:ℝ)) = 1/2 := by
      rw [Real.rpow_neg_one]
      norm_num
    calc (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s.re) ≤ (2:ℝ) ^ (-s.re) := hstep1
      _ ≤ (2:ℝ) ^ (-(1:ℝ)) := hstep2
      _ = 1/2 := hstep3
  have hfac_ne : ∀ 𝔭, (1 : ℂ) - x 𝔭 ≠ 0 := by
    intro 𝔭 h0
    have h1 : x 𝔭 = 1 := by linear_combination -h0
    have := hhalf 𝔭
    rw [h1] at this
    norm_num at this
  -- summability of the factor norms
  have hσsum : Summable (fun I : Chebotarev.NonzeroIdeal K =>
      (Ideal.absNorm I.1 : ℝ) ^ (-s.re)) := by
    have h1 := (Chebotarev.hasSum_nonzeroIdeal_absNorm_cpow K
      (s := ((s.re : ℝ) : ℂ)) (by simpa using hs)).summable
    have h1' : Summable (fun I : Chebotarev.NonzeroIdeal K =>
        (((Ideal.absNorm I.1 : ℝ) ^ (-s.re) : ℝ) : ℂ)) := by
      refine h1.congr (fun I => ?_)
      rw [show ((Ideal.absNorm I.1 : ℕ) : ℂ) = (((Ideal.absNorm I.1 : ℝ)) : ℂ) by
          push_cast; ring,
        show -(((s.re : ℝ)) : ℂ) = (((-s.re : ℝ)) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cpow (Nat.cast_nonneg _)]
    exact Complex.summable_ofReal.mp h1'
  have hprime_sum : Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} =>
      ‖x 𝔭‖) := by
    have hinj : Function.Injective
        (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} =>
          (⟨𝔭.1, 𝔭.2.2⟩ : Chebotarev.NonzeroIdeal K)) := by
      intro 𝔭 𝔮 h
      have h' : (⟨𝔭.1, 𝔭.2.2⟩ : Chebotarev.NonzeroIdeal K) = ⟨𝔮.1, 𝔮.2.2⟩ := h
      exact Subtype.ext (Subtype.mk_eq_mk.mp h')
    have hcomp := hσsum.comp_injective hinj
    exact hcomp.congr (fun 𝔭 => (hnormeq 𝔭).symm)
  -- the correction terms and their bound
  have hfbound : ∀ 𝔭, ‖(1 - x 𝔭)⁻¹ - 1‖ ≤ 2 * ‖x 𝔭‖ := by
    intro 𝔭
    have hid : (1 - x 𝔭)⁻¹ - 1 = x 𝔭 * (1 - x 𝔭)⁻¹ := by
      have he := hfac_ne 𝔭
      field_simp
      ring
    rw [hid, norm_mul]
    have hlow : (1:ℝ)/2 ≤ ‖1 - x 𝔭‖ := by
      have h1 : ‖(1:ℂ)‖ - ‖x 𝔭‖ ≤ ‖1 - x 𝔭‖ := norm_sub_norm_le _ _
      rw [norm_one] at h1
      linarith [hhalf 𝔭]
    have hinv : ‖(1 - x 𝔭)⁻¹‖ ≤ 2 := by
      rw [norm_inv]
      rw [show (2:ℝ) = (1/2)⁻¹ by norm_num]
      refine (inv_le_inv₀ ?_ (by norm_num)).mpr hlow
      have := hhalf 𝔭
      have h1 : (0:ℝ) < 1/2 := by norm_num
      linarith
    calc ‖x 𝔭‖ * ‖(1 - x 𝔭)⁻¹‖ ≤ ‖x 𝔭‖ * 2 :=
          mul_le_mul_of_nonneg_left hinv (norm_nonneg _)
      _ = 2 * ‖x 𝔭‖ := by ring
  have hfsum : Summable (fun 𝔭 => ‖(1 - x 𝔭)⁻¹ - 1‖) :=
    Summable.of_nonneg_of_le (fun 𝔭 => norm_nonneg _) hfbound (hprime_sum.mul_left 2)
  -- assemble
  have hcongr : (∏' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}, (1 - x 𝔭)⁻¹)
      = ∏' 𝔭, (1 + ((1 - x 𝔭)⁻¹ - 1)) :=
    tprod_congr (fun 𝔭 => by ring)
  rw [hcongr]
  refine tprod_one_add_ne_zero_of_summable (fun 𝔭 => ?_) hfsum
  rw [show (1:ℂ) + ((1 - x 𝔭)⁻¹ - 1) = (1 - x 𝔭)⁻¹ by ring]
  exact inv_ne_zero (hfac_ne 𝔭)

/-- `H = completedDedekindZetaEntire` does not vanish on `Re s > 1`. -/
theorem completedDedekindZetaEntire_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    completedDedekindZetaEntire K s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0] at hs
    simp at hs
    linarith
  have hs1 : s ≠ 1 := by
    intro h0
    rw [h0] at hs
    simp at hs
  rw [completedDedekindZetaEntire_eq K hs0 hs1,
    completedDedekindZeta_eq_of_one_lt_re K hs, completedZetaPrefactor]
  refine mul_ne_zero (mul_ne_zero hs0 ?_) (mul_ne_zero (mul_ne_zero ?_ ?_) ?_)
  · intro h0
    have := congrArg Complex.re h0
    simp at this
    linarith
  · intro h0
    have hbase : ((|discr K| : ℝ) : ℂ) ≠ 0 := by
      have h2 : |discr K| ≠ 0 := abs_ne_zero.mpr (NumberField.discr_ne_zero K)
      exact_mod_cast h2
    exact hbase ((Complex.cpow_eq_zero_iff _ _).mp h0).1
  · exact gammaFactor_ne_zero_of_re_pos K (by linarith)
  · exact dedekindZeta_ne_zero_of_one_lt_re K hs
/-- `H` does not vanish on `Re s < 0` (functional-equation reflection). -/
theorem completedDedekindZetaEntire_ne_zero_of_re_lt_zero {s : ℂ} (hs : s.re < 0) :
    completedDedekindZetaEntire K s ≠ 0 := by
  rw [← completedDedekindZetaEntire_one_sub K s]
  refine completedDedekindZetaEntire_ne_zero_of_one_lt_re K ?_
  rw [Complex.sub_re, Complex.one_re]
  linarith

/-- **Strip confinement**: every zero of `H` has real part in `[0, 1]`. -/
theorem re_mem_of_completedDedekindZetaEntire_eq_zero {ρ : ℂ}
    (h0 : completedDedekindZetaEntire K ρ = 0) : 0 ≤ ρ.re ∧ ρ.re ≤ 1 := by
  constructor
  · by_contra h
    exact completedDedekindZetaEntire_ne_zero_of_re_lt_zero K (by linarith) h0
  · by_contra h
    exact completedDedekindZetaEntire_ne_zero_of_one_lt_re K (by linarith) h0

/-- **Separation pigeonhole** (SP2-RECT R-e core): in any unit interval there is a
point at distance at least `1/(2(N+1))` from every member of a finite set of size at
most `N` — among the `N+1` midpoints of equal subintervals, at least one is far from
all of `S`, since distinct midpoints cannot share a close neighbour. -/
theorem exists_dist_ge_of_card_le {S : Finset ℝ} {N : ℕ} (hcard : S.card ≤ N) (a : ℝ) :
    ∃ t ∈ Set.Icc a (a + 1), ∀ s ∈ S, 1 / (2 * (N + 1)) ≤ |t - s| := by
  classical
  by_contra hcon
  push Not at hcon
  have hNpos : (0:ℝ) < 2 * ((N:ℝ) + 1) := by positivity
  -- each midpoint has a close member of S
  have hmid : ∀ k : Fin (N + 1), ∃ s ∈ S,
      |(a + (2 * (k:ℝ) + 1) / (2 * ((N:ℝ) + 1))) - s| < 1 / (2 * ((N:ℝ) + 1)) := by
    intro k
    have hk1 : (0:ℝ) ≤ (2 * (k:ℝ) + 1) / (2 * ((N:ℝ) + 1)) := by positivity
    have hk2 : (2 * (k:ℝ) + 1) / (2 * ((N:ℝ) + 1)) ≤ 1 := by
      rw [div_le_one hNpos]
      have : (k:ℝ) ≤ N := by
        have := k.2
        have h1 : (k:ℕ) ≤ N := by omega
        exact_mod_cast h1
      linarith
    have hmem : a + (2 * (k:ℝ) + 1) / (2 * ((N:ℝ) + 1)) ∈ Set.Icc a (a + 1) := by
      rw [Set.mem_Icc]
      constructor <;> linarith
    obtain ⟨s, hs, hlt⟩ := hcon _ hmem
    exact ⟨s, hs, by linarith [hlt]⟩
  choose f hfS hfclose using hmid
  -- pigeonhole: N+1 midpoints into ≤ N members
  have hlt : S.card < (Finset.univ : Finset (Fin (N + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨k, _, k', hk'mem, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt (fun k _ => hfS k)
  -- two distinct midpoints within 1/(N+1) of the same point: contradiction
  have h1 := hfclose k
  have h2 := hfclose k'
  rw [heq] at h1
  have htri : |(a + (2 * (k:ℝ) + 1) / (2 * ((N:ℝ) + 1)))
      - (a + (2 * (k':ℝ) + 1) / (2 * ((N:ℝ) + 1)))| < 1 / ((N:ℝ) + 1) := by
    calc |(a + (2 * (k:ℝ) + 1) / (2 * ((N:ℝ) + 1)))
        - (a + (2 * (k':ℝ) + 1) / (2 * ((N:ℝ) + 1)))|
        ≤ |(a + (2 * (k:ℝ) + 1) / (2 * ((N:ℝ) + 1))) - f k'|
          + |f k' - (a + (2 * (k':ℝ) + 1) / (2 * ((N:ℝ) + 1)))| := abs_sub_le _ _ _
      _ < 1 / (2 * ((N:ℝ) + 1)) + 1 / (2 * ((N:ℝ) + 1)) := by
          rw [abs_sub_comm (f k')]
          exact add_lt_add h1 h2
      _ = 1 / ((N:ℝ) + 1) := by
          field_simp
          ring
  have hdiff : |(a + (2 * (k:ℝ) + 1) / (2 * ((N:ℝ) + 1)))
      - (a + (2 * (k':ℝ) + 1) / (2 * ((N:ℝ) + 1)))|
      = |(k:ℝ) - (k':ℝ)| / ((N:ℝ) + 1) := by
    rw [show (a + (2 * (k:ℝ) + 1) / (2 * ((N:ℝ) + 1)))
        - (a + (2 * (k':ℝ) + 1) / (2 * ((N:ℝ) + 1)))
        = ((k:ℝ) - (k':ℝ)) / ((N:ℝ) + 1) by field_simp; ring]
    rw [abs_div]
    congr 1
    rw [abs_of_pos (by positivity : (0:ℝ) < (N:ℝ) + 1)]
  have hge : (1:ℝ) ≤ |(k:ℝ) - (k':ℝ)| := by
    have hkk' : (k:ℕ) ≠ (k':ℕ) := fun h => hne (Fin.ext h)
    have h1 : ((k:ℕ) : ℤ) ≠ ((k':ℕ) : ℤ) := by exact_mod_cast hkk'
    have h2 : (1:ℤ) ≤ |((k:ℕ) : ℤ) - ((k':ℕ) : ℤ)| := Int.one_le_abs (sub_ne_zero_of_ne h1)
    have h3 : ((|((k:ℕ) : ℤ) - ((k':ℕ) : ℤ)| : ℤ) : ℝ) = |(k:ℝ) - (k':ℝ)| := by
      push_cast
      ring_nf
    calc (1:ℝ) = ((1:ℤ) : ℝ) := by norm_num
      _ ≤ ((|((k:ℕ) : ℤ) - ((k':ℕ) : ℤ)| : ℤ) : ℝ) := by exact_mod_cast h2
      _ = |(k:ℝ) - (k':ℝ)| := h3
  rw [hdiff] at htri
  have : (1:ℝ) / ((N:ℝ) + 1) ≤ |(k:ℝ) - (k':ℝ)| / ((N:ℝ) + 1) := by
    gcongr
  linarith

/-- `H` is not identically zero near any point (identity theorem with the witness
`H(2) ≠ 0`), so its meromorphic order is everywhere finite. -/
theorem meromorphicOrderAt_completedDedekindZetaEntire_ne_top (u : ℂ) :
    meromorphicOrderAt (completedDedekindZetaEntire K) u ≠ ⊤ := by
  have hHanal : ∀ ζ : ℂ, AnalyticAt ℂ (completedDedekindZetaEntire K) ζ :=
    analyticAt_completedDedekindZetaEntire K
  intro htop
  rw [(hHanal u).meromorphicOrderAt_eq] at htop
  have hordtop : analyticOrderAt (completedDedekindZetaEntire K) u = ⊤ :=
    ENat.map_eq_top_iff.mp htop
  have hev : ∀ᶠ z in nhds u, completedDedekindZetaEntire K z = 0 :=
    analyticOrderAt_eq_top.mp hordtop
  have hzero : Set.EqOn (completedDedekindZetaEntire K) 0 Set.univ := by
    refine AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (fun ζ _ => hHanal ζ) isPreconnected_univ (Set.mem_univ u) hev
  have h2 : completedDedekindZetaEntire K (2 : ℂ) ≠ 0 := by
    refine completedDedekindZetaEntire_ne_zero_of_one_lt_re K ?_
    norm_num
  exact h2 (hzero (Set.mem_univ _))

/-- Points where the divisor of `H` is nonzero are zeros of `H`. -/
theorem completedDedekindZetaEntire_eq_zero_of_divisor_ne_zero {U : Set ℂ} {u : ℂ}
    (hu : (MeromorphicOn.divisor (completedDedekindZetaEntire K) U) u ≠ 0) :
    completedDedekindZetaEntire K u = 0 := by
  by_contra hne
  apply hu
  rw [MeromorphicOn.divisor_def]
  by_cases hcond : MeromorphicOn (completedDedekindZetaEntire K) U ∧ u ∈ U
  · rw [if_pos hcond]
    rw [(analyticAt_completedDedekindZetaEntire K u).meromorphicOrderAt_eq,
      analyticOrderAt_eq_zero.mpr (Or.inr hne)]
    simp
  · rw [if_neg hcond]

/-- Conversely, on an open set the divisor of `H` is nonzero at every zero of `H`. -/
theorem divisor_ne_zero_of_completedDedekindZetaEntire_eq_zero {U : Set ℂ} {u : ℂ}
    (huU : u ∈ U) (h0 : completedDedekindZetaEntire K u = 0) :
    (MeromorphicOn.divisor (completedDedekindZetaEntire K) U) u ≠ 0 := by
  have hHanal : ∀ ζ : ℂ, AnalyticAt ℂ (completedDedekindZetaEntire K) ζ :=
    analyticAt_completedDedekindZetaEntire K
  have hm : MeromorphicOn (completedDedekindZetaEntire K) U := fun ζ _ =>
    (hHanal ζ).meromorphicAt
  rw [MeromorphicOn.divisor_apply hm huU]
  intro hcon
  rcases WithTop.untop₀_eq_zero.mp hcon with h | h
  · obtain ⟨c, hc0, hc⟩ :=
      tendsto_ne_zero_of_meromorphicOrderAt_eq_zero ((hHanal u).meromorphicAt) h
    have hcont : Filter.Tendsto (completedDedekindZetaEntire K)
        (nhdsWithin u {u}ᶜ) (nhds (completedDedekindZetaEntire K u)) :=
      ((hHanal u).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    have huniq := tendsto_nhds_unique hc hcont
    rw [h0] at huniq
    exact hc0 huniq
  · exact meromorphicOrderAt_completedDedekindZetaEntire_ne_top K u h

/-- For `1 ≤ T`, one has `1 ≤ log (2 + T)` (since `2 + T ≥ e`). Base estimate for the
`log`-height bounds along the explicit-formula contour. -/
theorem one_le_log_two_add {T : ℝ} (hT : 1 ≤ T) : (1:ℝ) ≤ Real.log (2 + T) := by
  have he : Real.exp 1 ≤ 2 + T := by
    have := Real.exp_one_lt_d9
    linarith
  calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log (2 + T) := Real.log_le_log (Real.exp_pos 1) he

/-- `log`-doubling: if `1 ≤ B`, `0 < s` and `s ≤ 2(2 + B)` then
`log s ≤ 2 · log (2 + B)`. Compares a height in the window `[T₀, T₀+1]` to the base
height `T₀` at the cost of a factor `2` (from `log 2 ≤ 1`). -/
theorem log_le_two_mul_log_two_add {s B : ℝ} (hB : 1 ≤ B) (hs0 : 0 < s) (hs : s ≤ (2 + B) * 2) :
    Real.log s ≤ 2 * Real.log (2 + B) := by
  calc Real.log s ≤ Real.log ((2 + B) * 2) := Real.log_le_log hs0 hs
    _ = Real.log (2 + B) + Real.log 2 := by rw [Real.log_mul (by linarith) (by norm_num)]
    _ ≤ 2 * Real.log (2 + B) := by
        have h2 : Real.log 2 ≤ 1 := by
          have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
          linarith
        have := one_le_log_two_add hB
        linarith

/-- **Two-sided good heights** (SP2-RECT R-e, both edges): every unit window
`[T₀, T₀+1]` at height `T₀ ≥ A+5` contains a height `T` separated from every zero
ordinate in BOTH directions: `|T − Im ρ| ≥ c/log(2+T₀)` and `|T + Im ρ| ≥ c/log(2+T₀)`
— the latter is the separation of the bottom edge `Im = −T` of the contour rectangle. -/
theorem exists_good_height :
    ∃ A : ℝ, 2 ≤ A ∧ ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ T₀ : ℝ, A + 5 ≤ T₀ →
      ∃ T ∈ Set.Icc T₀ (T₀ + 1), ∀ ρ : ℂ, completedDedekindZetaEntire K ρ = 0 →
        c / Real.log (2 + T₀) ≤ |T - ρ.im| ∧ c / Real.log (2 + T₀) ≤ |T + ρ.im| := by
  classical
  obtain ⟨A, hA2, cL, hcL, hlow⟩ := exists_H_center_lower K
  obtain ⟨Cc, hCc, hcount⟩ := exists_ball_zero_count_big K A hA2 cL hcL hlow
  refine ⟨A, hA2, min 1 (1 / (2 * (4 * Cc + 2))), by positivity,
    min_le_left _ _, fun T₀ hT₀ => ?_⟩
  have hT₀pos : (7:ℝ) ≤ T₀ := by linarith
  have hlog1 : (1:ℝ) ≤ Real.log (2 + T₀) := one_le_log_two_add (by linarith)
  have hHanal : ∀ ζ : ℂ, AnalyticAt ℂ (completedDedekindZetaEntire K) ζ :=
    analyticAt_completedDedekindZetaEntire K
  -- the two windows: ordinates near +T₀ and near −T₀
  have hlogle : ∀ Tc : ℝ, |Tc| = T₀ + 1/2 →
      Real.log (2 + |Tc|) ≤ 2 * Real.log (2 + T₀) := by
    intro Tc hTc
    rw [hTc]
    exact log_le_two_mul_log_two_add (by linarith) (by linarith) (by linarith)
  -- a generic window package: for a center height Tc, the ordinate image of the
  -- divisor support of the window is a finset of size ≤ 2·Cc·log(2+T₀)
  have hwindow : ∀ Tc : ℝ, |Tc| = T₀ + 1/2 →
      ∃ S : Finset ℝ, ((S.card : ℝ) ≤ 2 * Cc * Real.log (2 + T₀)
        ∧ ∀ ρ : ℂ, completedDedekindZetaEntire K ρ = 0 →
          ρ.im ∈ Set.Ioo (Tc - 3/2) (Tc + 3/2) → ρ.im ∈ S) := by
    intro Tc hTc
    set c₀ : ℂ := (A : ℂ) + (Tc : ℂ) * Complex.I with hc₀
    set V : Set ℂ := Set.Ioo (-1 : ℝ) 2 ×ℂ Set.Ioo (Tc - 3/2) (Tc + 3/2) with hV
    have hVo : IsOpen V := isOpen_Ioo.reProdIm isOpen_Ioo
    set D : ℂ → ℤ := fun u => (MeromorphicOn.divisor (completedDedekindZetaEntire K) V) u
      with hD
    have hDnn : ∀ u, 0 ≤ D u := fun u =>
      (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (fun ζ _ => hHanal ζ)) u
    obtain ⟨R₀, hR₀⟩ := ((Metric.isBounded_Ioo (-1:ℝ) 2).reProdIm
      (Metric.isBounded_Ioo (Tc - 3/2) (Tc + 3/2))).subset_closedBall (0 : ℂ)
    have hfin : (Function.support D).Finite :=
      MeromorphicOn.divisor_support_finite_of_subset
        (fun ζ _ => (hHanal ζ).meromorphicAt) (isCompact_closedBall (0:ℂ) R₀) hR₀
    refine ⟨hfin.toFinset.image Complex.im, ?_, ?_⟩
    · -- count
      have hVball : V ⊆ Metric.closedBall c₀ (A + 2) := by
        intro ζ hζ
        rw [hV, Complex.mem_reProdIm, Set.mem_Ioo, Set.mem_Ioo] at hζ
        rw [Metric.mem_closedBall, dist_eq_norm]
        have hre : ((ζ - c₀).re) = ζ.re - A := by
          rw [hc₀]
          simp
        have him : ((ζ - c₀).im) = ζ.im - Tc := by
          rw [hc₀]
          simp
        have hsq : ‖ζ - c₀‖^2 = (ζ.re - A)^2 + (ζ.im - Tc)^2 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre, him]
          ring
        have h1 : (ζ.re - A)^2 ≤ (A+1)^2 := by
          have := hζ.1
          nlinarith [this.1, this.2]
        have h2 : (ζ.im - Tc)^2 ≤ (3/2)^2 := by
          have := hζ.2
          nlinarith [this.1, this.2]
        nlinarith [norm_nonneg (ζ - c₀), hsq]
      have h1 : (hfin.toFinset.image Complex.im).card ≤ hfin.toFinset.card :=
        Finset.card_image_le
      have h2 : hfin.toFinset.card ≤ ∑ u ∈ hfin.toFinset, (D u).toNat := by
        rw [Finset.card_eq_sum_ones]
        refine Finset.sum_le_sum ?_
        intro u hu
        have hne : D u ≠ 0 := Function.mem_support.mp (hfin.mem_toFinset.mp hu)
        have := hDnn u
        omega
      set Dcl : ℂ → ℤ := fun u => (MeromorphicOn.divisor (completedDedekindZetaEntire K)
        (Metric.closedBall c₀ (A+2))) u with hDcl
      have hmcl : MeromorphicOn (completedDedekindZetaEntire K)
          (Metric.closedBall c₀ (A+2)) := fun ζ _ => (hHanal ζ).meromorphicAt
      have hmV : MeromorphicOn (completedDedekindZetaEntire K) V := fun ζ _ =>
        (hHanal ζ).meromorphicAt
      have hfincl : (Function.support Dcl).Finite :=
        MeromorphicOn.divisor_support_finite_of_subset hmcl
          (isCompact_closedBall c₀ (A+2)) subset_rfl
      have hDclnn : ∀ u, 0 ≤ Dcl u := fun u =>
        (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (fun ζ _ => hHanal ζ)) u
      have hpt : ∀ u, D u ≤ Dcl u := by
        intro u
        by_cases hu : u ∈ V
        · rw [hD, hDcl]
          simp only
          rw [MeromorphicOn.divisor_apply hmV hu,
            MeromorphicOn.divisor_apply hmcl (hVball hu)]
        · rw [hD]
          simp only
          rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]
          exact hDclnn u
      have hFsub : hfin.toFinset ⊆ hfincl.toFinset := by
        intro u hu
        have hu' := Function.mem_support.mp (hfin.mem_toFinset.mp hu)
        refine hfincl.mem_toFinset.mpr (Function.mem_support.mpr ?_)
        intro h0
        refine hu' (le_antisymm ?_ (hDnn u))
        rw [← h0]
        exact hpt u
      have e1 : ((∑ u ∈ hfin.toFinset, (D u).toNat : ℕ) : ℤ)
          = ∑ u ∈ hfin.toFinset, D u := by
        push_cast
        refine Finset.sum_congr rfl (fun u _ => Int.toNat_of_nonneg (hDnn u))
      have e2 : ∑ u ∈ hfin.toFinset, D u ≤ ∑ u ∈ hfincl.toFinset, Dcl u := by
        calc ∑ u ∈ hfin.toFinset, D u = ∑ u ∈ hfincl.toFinset, D u := by
              refine Finset.sum_subset hFsub (fun u _ hu => ?_)
              by_contra h0
              exact hu (hfin.mem_toFinset.mpr (Function.mem_support.mpr h0))
          _ ≤ ∑ u ∈ hfincl.toFinset, Dcl u := Finset.sum_le_sum (fun u _ => hpt u)
      have e3 : ∑ u ∈ hfincl.toFinset, Dcl u = ∑ᶠ u, Dcl u :=
        (finsum_eq_sum Dcl hfincl).symm
      have hcnt := hcount Tc (by rw [hTc]; linarith)
      calc ((hfin.toFinset.image Complex.im).card : ℝ)
          ≤ ((∑ u ∈ hfin.toFinset, (D u).toNat : ℕ) : ℝ) := by
            exact_mod_cast le_trans h1 h2
        _ ≤ ((∑ᶠ u, Dcl u : ℤ) : ℝ) := by
            have hint : ((∑ u ∈ hfin.toFinset, (D u).toNat : ℕ) : ℤ) ≤ ∑ᶠ u, Dcl u := by
              rw [e1, ← e3]
              exact e2
            exact_mod_cast hint
        _ ≤ Cc * Real.log (2 + |Tc|) := hcnt
        _ ≤ Cc * (2 * Real.log (2 + T₀)) :=
            mul_le_mul_of_nonneg_left (hlogle Tc hTc) hCc.le
        _ = 2 * Cc * Real.log (2 + T₀) := by ring
    · -- membership
      intro ρ hρ hρim
      have hstrip := re_mem_of_completedDedekindZetaEntire_eq_zero K hρ
      have hρV : ρ ∈ V := by
        rw [hV, Complex.mem_reProdIm]
        exact ⟨Set.mem_Ioo.mpr ⟨by linarith [hstrip.1], by linarith [hstrip.2]⟩, hρim⟩
      have hDρ : D ρ ≠ 0 :=
        divisor_ne_zero_of_completedDedekindZetaEntire_eq_zero K hρV hρ
      exact Finset.mem_image.mpr ⟨ρ, hfin.mem_toFinset.mpr
        (Function.mem_support.mpr hDρ), rfl⟩
  obtain ⟨Sp, hSpcard, hSpmem⟩ := hwindow (T₀ + 1/2) (by rw [abs_of_pos (by linarith)])
  obtain ⟨Sm, hSmcard, hSmmem⟩ := hwindow (-(T₀ + 1/2)) (by rw [abs_neg,
    abs_of_pos (by linarith)])
  -- combined ordinate set: window ordinates and negated mirror-window ordinates
  set S : Finset ℝ := Sp ∪ Sm.image (fun x => -x) with hSdef
  have hScard : (S.card : ℝ) ≤ 4 * Cc * Real.log (2 + T₀) := by
    calc (S.card : ℝ) ≤ ((Sp.card + (Sm.image (fun x => -x)).card : ℕ) : ℝ) := by
          exact_mod_cast Finset.card_union_le _ _
      _ ≤ (Sp.card : ℝ) + (Sm.card : ℝ) := by
          push_cast
          have := Finset.card_image_le (f := fun x : ℝ => -x) (s := Sm)
          have h1 : ((Sm.image (fun x => -x)).card : ℝ) ≤ (Sm.card : ℝ) := by
            exact_mod_cast this
          linarith
      _ ≤ 2 * Cc * Real.log (2 + T₀) + 2 * Cc * Real.log (2 + T₀) := by
          linarith [hSpcard, hSmcard]
      _ = 4 * Cc * Real.log (2 + T₀) := by ring
  obtain ⟨T, hTmem, hTsep⟩ := exists_dist_ge_of_card_le (le_refl S.card) T₀
  refine ⟨T, hTmem, fun ρ hρ => ?_⟩
  have hcpos : (0:ℝ) < min 1 (1 / (2 * (4 * Cc + 2))) := by positivity
  have hlogpos : (0:ℝ) < Real.log (2 + T₀) := by linarith
  -- the pigeonhole distance beats c/log
  have hbeats : min 1 (1 / (2 * (4 * Cc + 2))) / Real.log (2 + T₀)
      ≤ 1 / (2 * ((S.card : ℝ) + 1)) := by
    rw [div_le_div_iff₀ hlogpos (by positivity), one_mul]
    have hc2 : min 1 (1 / (2 * (4 * Cc + 2))) ≤ 1 / (2 * (4 * Cc + 2)) :=
      min_le_right _ _
    have hkey : (2 : ℝ) * ((S.card : ℝ) + 1)
        ≤ (2 * (4 * Cc + 2)) * Real.log (2 + T₀) := by
      nlinarith [hScard, hlog1, hCc.le]
    have hden : (2 * (4 * Cc + 2)) ≠ 0 := by positivity
    calc min 1 (1 / (2 * (4 * Cc + 2))) * (2 * ((S.card : ℝ) + 1))
        ≤ (1 / (2 * (4 * Cc + 2))) * ((2 * (4 * Cc + 2)) * Real.log (2 + T₀)) := by
          refine mul_le_mul hc2 hkey (by positivity) (by positivity)
      _ = Real.log (2 + T₀) := by
          field_simp
  have hfar : ∀ x : ℝ, x ∉ Set.Ioo (T₀ - 1) (T₀ + 2) → (1:ℝ) ≤ |T - x| := by
    intro x hx
    rw [Set.mem_Ioo] at hx
    push Not at hx
    rw [Set.mem_Icc] at hTmem
    rcases le_or_gt x (T₀ - 1) with h | h
    · rw [abs_of_pos (by linarith)]
      linarith
    · have h2 := hx h
      rw [abs_of_neg (by linarith)]
      linarith
  have hsmall : min 1 (1 / (2 * (4 * Cc + 2))) / Real.log (2 + T₀) ≤ 1 := by
    calc min 1 (1 / (2 * (4 * Cc + 2))) / Real.log (2 + T₀)
        ≤ 1 / 1 := by
          refine div_le_div₀ (by norm_num) (min_le_left _ _) (by norm_num) hlog1
      _ = 1 := by norm_num
  constructor
  · -- top edge separation
    by_cases hwin : ρ.im ∈ Set.Ioo (T₀ - 1) (T₀ + 2)
    · have hmem : ρ.im ∈ S := by
        rw [hSdef]
        refine Finset.mem_union_left _ (hSpmem ρ hρ ?_)
        rw [Set.mem_Ioo] at hwin ⊢
        constructor <;> [linarith [hwin.1]; linarith [hwin.2]]
      exact le_trans hbeats (hTsep ρ.im hmem)
    · exact le_trans hsmall (hfar ρ.im hwin)
  · -- bottom edge separation: |T + ρ.im| = |T - (-ρ.im)|
    rw [show T + ρ.im = T - (-ρ.im) by ring]
    by_cases hwin : (-ρ.im) ∈ Set.Ioo (T₀ - 1) (T₀ + 2)
    · have hmem : (-ρ.im) ∈ S := by
        rw [hSdef]
        refine Finset.mem_union_right _ ?_
        refine Finset.mem_image.mpr ⟨ρ.im, ?_, rfl⟩
        refine hSmmem ρ hρ ?_
        rw [Set.mem_Ioo] at hwin ⊢
        constructor <;> [linarith [hwin.2]; linarith [hwin.1]]
      exact le_trans hbeats (hTsep (-ρ.im) hmem)
    · exact le_trans hsmall (hfar (-ρ.im) hwin)

/-- **Contour heights** (SP2-RECT R-f): heights `T ∈ [T₀, T₀+1]` at which both
horizontal edges `Im = ±T` of the explicit-formula rectangle are zero-free for `H`
and carry the Landau bound `‖H'/H‖ ≤ C·log²(2+T₀)` across the strip `-1/4 ≤ Re ≤ 5/4`.
Combines the two-sided good-height separation with the exported zero count and the
partial-fraction decomposition of AC-A5. -/
theorem exists_contour_height :
    ∃ A : ℝ, 2 ≤ A ∧ ∃ c C : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 < C ∧ ∀ T₀ : ℝ, A + 5 ≤ T₀ →
      ∃ T ∈ Set.Icc T₀ (T₀ + 1),
        (∀ ρ : ℂ, completedDedekindZetaEntire K ρ = 0 →
          c / Real.log (2 + T₀) ≤ |T - ρ.im| ∧ c / Real.log (2 + T₀) ≤ |T + ρ.im|)
        ∧ (∀ σ : ℝ, -(1/4) ≤ σ → σ ≤ 5/4 →
            completedDedekindZetaEntire K ((σ:ℂ) + (T:ℂ) * Complex.I) ≠ 0
            ∧ ‖logDeriv (completedDedekindZetaEntire K) ((σ:ℂ) + (T:ℂ) * Complex.I)‖
              ≤ C * (Real.log (2 + T₀))^2)
        ∧ ∀ σ : ℝ, -(1/4) ≤ σ → σ ≤ 5/4 →
            completedDedekindZetaEntire K ((σ:ℂ) + ((-T:ℝ):ℂ) * Complex.I) ≠ 0
            ∧ ‖logDeriv (completedDedekindZetaEntire K) ((σ:ℂ) + ((-T:ℝ):ℂ) * Complex.I)‖
              ≤ C * (Real.log (2 + T₀))^2 := by
  classical
  obtain ⟨A₁, hA₁2, C₁, hC₁, hmain⟩ := exists_logDeriv_partial_fractions K
  obtain ⟨A₂, hA₂2, c₂, hc₂, hc₂1, hgood⟩ := exists_good_height K
  refine ⟨max A₁ A₂, le_trans hA₁2 (le_max_left _ _),
    c₂, 2*C₁/c₂ + 2*C₁, hc₂, hc₂1, by positivity, fun T₀ hT₀ => ?_⟩
  have hT₀A₁ : A₁ + 5 ≤ T₀ := by
    have := le_max_left A₁ A₂
    linarith
  have hT₀A₂ : A₂ + 5 ≤ T₀ := by
    have := le_max_right A₁ A₂
    linarith
  have hT₀7 : (7:ℝ) ≤ T₀ := by linarith
  have hlog1 : (1:ℝ) ≤ Real.log (2 + T₀) := one_le_log_two_add (by linarith)
  have hlogpos : (0:ℝ) < Real.log (2 + T₀) := by linarith
  obtain ⟨T, hTmem, hTsep⟩ := hgood T₀ hT₀A₂
  rw [Set.mem_Icc] at hTmem
  have hTpos : (0:ℝ) < T := by linarith
  -- log comparison for heights in the window
  have hlogT : Real.log (2 + T) ≤ 2 * Real.log (2 + T₀) :=
    log_le_two_mul_log_two_add (by linarith) (by linarith) (by linarith)
  -- the shared per-edge argument
  have hedge : ∀ T' : ℝ, |T'| = T →
      (∀ ρ : ℂ, completedDedekindZetaEntire K ρ = 0 →
        c₂ / Real.log (2 + T₀) ≤ |T' - ρ.im|) →
      ∀ σ : ℝ, -(1/4) ≤ σ → σ ≤ 5/4 →
        completedDedekindZetaEntire K ((σ:ℂ) + (T':ℂ) * Complex.I) ≠ 0
        ∧ ‖logDeriv (completedDedekindZetaEntire K) ((σ:ℂ) + (T':ℂ) * Complex.I)‖
          ≤ (2*C₁/c₂ + 2*C₁) * (Real.log (2 + T₀))^2 := by
    intro T' hT'abs hsep σ hσ1 hσ2
    have hT'A₁ : A₁ + 5 ≤ |T'| := by
      rw [hT'abs]
      linarith
    obtain ⟨hcnt, hpf⟩ := hmain T' hT'A₁
    set s : ℂ := (σ:ℂ) + (T':ℂ) * Complex.I with hs
    have hsim : s.im = T' := by
      rw [hs]
      simp
    have hsre : s.re = σ := by
      rw [hs]
      simp
    -- s is not a zero
    have hHs : completedDedekindZetaEntire K s ≠ 0 := by
      intro h0
      have := hsep s h0
      rw [hsim, sub_self, abs_zero] at this
      have : (0:ℝ) < c₂ / Real.log (2 + T₀) := by positivity
      linarith
    refine ⟨hHs, ?_⟩
    -- s is in the A5 slab ball
    have hsball : s ∈ Metric.closedBall ((A₁ : ℂ) + (T' : ℂ) * Complex.I) (A₁ + 5/4) := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hdiff : s - ((A₁ : ℂ) + (T' : ℂ) * Complex.I) = ((σ - A₁ : ℝ) : ℂ) := by
        rw [hs]
        push_cast
        ring
      rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    have hbound := hpf s hsball hHs
    -- the divisor data
    set D : ℂ → ℤ := fun u => (MeromorphicOn.divisor (completedDedekindZetaEntire K)
      (Metric.ball ((A₁ : ℂ) + (T' : ℂ) * Complex.I) (A₁ + 2))) u with hD
    have hDnn : ∀ u, 0 ≤ D u := fun u =>
      (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (fun ζ _ =>
        analyticAt_completedDedekindZetaEntire K ζ)) u
    obtain ⟨R₀, hR₀⟩ := (Metric.isBounded_ball (x := (A₁ : ℂ) + (T' : ℂ) * Complex.I)
      (r := A₁ + 2)).subset_closedBall (0 : ℂ)
    have hfin : (Function.support D).Finite :=
      MeromorphicOn.divisor_support_finite_of_subset
        (fun ζ _ => (analyticAt_completedDedekindZetaEntire K ζ).meromorphicAt)
        (isCompact_closedBall (0:ℂ) R₀) hR₀
    -- separation for every support point
    have hsep' : ∀ u ∈ hfin.toFinset, c₂ / Real.log (2 + T₀) ≤ ‖s - u‖ := by
      intro u hu
      have hHu : completedDedekindZetaEntire K u = 0 :=
        completedDedekindZetaEntire_eq_zero_of_divisor_ne_zero K
          (Function.mem_support.mp (hfin.mem_toFinset.mp hu))
      calc c₂ / Real.log (2 + T₀) ≤ |T' - u.im| := hsep u hHu
        _ = |(s - u).im| := by rw [show (s - u).im = T' - u.im by rw [Complex.sub_im, hsim]]
        _ ≤ ‖s - u‖ := Complex.abs_im_le_norm _
      -- the sum bound
    have hsum : ‖∑ᶠ u, ((D u : ℂ)) / (s - u)‖
        ≤ C₁ * Real.log (2 + |T'|) * (Real.log (2 + T₀) / c₂) := by
      have hsub : (Function.support (fun u => ((D u : ℂ)) / (s - u))) ⊆ hfin.toFinset := by
        intro u hu
        rw [Function.mem_support] at hu
        refine hfin.mem_toFinset.mpr (Function.mem_support.mpr ?_)
        intro h0
        rw [h0] at hu
        simp at hu
      rw [finsum_eq_sum_of_support_subset _ hsub]
      calc ‖∑ u ∈ hfin.toFinset, ((D u : ℂ)) / (s - u)‖
          ≤ ∑ u ∈ hfin.toFinset, ‖((D u : ℂ)) / (s - u)‖ := norm_sum_le _ _
        _ ≤ ∑ u ∈ hfin.toFinset, (D u : ℝ) * (Real.log (2 + T₀) / c₂) := by
            refine Finset.sum_le_sum (fun u hu => ?_)
            rw [norm_div]
            have hDu : ‖((D u : ℂ))‖ = (D u : ℝ) := by
              rw [show ((D u : ℂ)) = (((D u : ℝ)) : ℂ) by push_cast; ring,
                Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by exact_mod_cast hDnn u)]
            rw [hDu]
            have hpos : (0:ℝ) < c₂ / Real.log (2 + T₀) := by positivity
            have hlow := hsep' u hu
            have hnorm_pos : (0:ℝ) < ‖s - u‖ := lt_of_lt_of_le hpos hlow
            rw [div_eq_mul_inv]
            refine mul_le_mul_of_nonneg_left ?_ (by exact_mod_cast hDnn u)
            refine le_trans ((inv_le_inv₀ hnorm_pos hpos).mpr hlow) (le_of_eq ?_)
            rw [inv_div]
        _ = ((∑ u ∈ hfin.toFinset, D u : ℤ) : ℝ) * (Real.log (2 + T₀) / c₂) := by
            rw [← Finset.sum_mul]
            push_cast
            ring
        _ ≤ C₁ * Real.log (2 + |T'|) * (Real.log (2 + T₀) / c₂) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            have hfs : ((∑ u ∈ hfin.toFinset, D u : ℤ) : ℝ) = ((∑ᶠ u, D u : ℤ) : ℝ) := by
              rw [finsum_eq_sum D hfin]
            rw [hfs]
            exact hcnt
    -- assemble the edge bound
    have hTT : Real.log (2 + |T'|) ≤ 2 * Real.log (2 + T₀) := by
      rw [hT'abs]
      exact hlogT
    have htri : ‖logDeriv (completedDedekindZetaEntire K) s‖
        ≤ ‖logDeriv (completedDedekindZetaEntire K) s
            - ∑ᶠ u, ((D u : ℂ)) / (s - u)‖ + ‖∑ᶠ u, ((D u : ℂ)) / (s - u)‖ :=
      norm_le_norm_sub_add _ _
    have hfac1 : (0:ℝ) ≤ 1 + Real.log (2 + T₀) / c₂ := by positivity
    calc ‖logDeriv (completedDedekindZetaEntire K) s‖
        ≤ ‖logDeriv (completedDedekindZetaEntire K) s
            - ∑ᶠ u, ((D u : ℂ)) / (s - u)‖ + ‖∑ᶠ u, ((D u : ℂ)) / (s - u)‖ := htri
      _ ≤ C₁ * Real.log (2 + |T'|)
          + C₁ * Real.log (2 + |T'|) * (Real.log (2 + T₀) / c₂) :=
          add_le_add hbound hsum
      _ = C₁ * Real.log (2 + |T'|) * (1 + Real.log (2 + T₀) / c₂) := by ring
      _ ≤ C₁ * (2 * Real.log (2 + T₀)) * (1 + Real.log (2 + T₀) / c₂) := by
          refine mul_le_mul_of_nonneg_right ?_ hfac1
          exact mul_le_mul_of_nonneg_left hTT hC₁.le
      _ ≤ (2*C₁/c₂ + 2*C₁) * (Real.log (2 + T₀))^2 := by
          rw [show (2*C₁/c₂ + 2*C₁) * (Real.log (2 + T₀))^2
              = C₁ * (2 * Real.log (2 + T₀))
                * (Real.log (2 + T₀)/c₂ + Real.log (2 + T₀)) by ring]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith
  -- both edges
  refine ⟨T, Set.mem_Icc.mpr hTmem, hTsep, ?_, ?_⟩
  · exact hedge T (abs_of_pos hTpos) (fun ρ hρ => (hTsep ρ hρ).1)
  · refine hedge (-T) (by rw [abs_neg]; exact abs_of_pos hTpos) (fun ρ hρ => ?_)
    have h2 := (hTsep ρ hρ).2
    calc c₂ / Real.log (2 + T₀) ≤ |T + ρ.im| := h2
      _ = |(-T) - ρ.im| := by
          rw [show (-T) - ρ.im = -(T + ρ.im) by ring, abs_neg]

/-- **Zero capture on the explicit-formula rectangle** (SP2-RECT R-g, step 1): for a
half-width `0 < a ≤ 1/4`, a positive height `T` at which both horizontal edges are
zero-free (as produced by `exists_contour_height`), and `Φ` holomorphic on the closed
rectangle `[-a, 1+a] × [-T, T]`,

`∮_{∂R} Φ·H'/H = 2πi·∑_ρ m_ρ·Φ(ρ)`,

the sum over the divisor of `H` on the open rectangle. The vertical edges are
zero-free automatically (`Re = -a < 0` and `Re = 1+a > 1`). -/
theorem rectangle_zero_capture {a T : ℝ} (ha : 0 < a) (ha' : a ≤ 1/4) (hT : 0 < T)
    {Φ : ℂ → ℂ}
    (hΦ : ∀ ζ ∈ Set.uIcc (-a) (1+a) ×ℂ Set.uIcc (-T) T, DifferentiableAt ℂ Φ ζ)
    (htop : ∀ σ : ℝ, -a ≤ σ → σ ≤ 1+a →
      completedDedekindZetaEntire K ((σ:ℂ) + (T:ℂ) * Complex.I) ≠ 0)
    (hbot : ∀ σ : ℝ, -a ≤ σ → σ ≤ 1+a →
      completedDedekindZetaEntire K ((σ:ℂ) + ((-T:ℝ):ℂ) * Complex.I) ≠ 0) :
    rectangleIntegral (fun ζ => Φ ζ * logDeriv (completedDedekindZetaEntire K) ζ)
        (((-a : ℝ):ℂ) + ((-T:ℝ):ℂ) * Complex.I) (((1+a : ℝ):ℂ) + ((T:ℝ):ℂ) * Complex.I)
      = 2 * Real.pi * Complex.I
        * ∑ᶠ ρ, (((MeromorphicOn.divisor (completedDedekindZetaEntire K)
            (Set.Ioo (-a) (1+a) ×ℂ Set.Ioo (-T) T)) ρ : ℂ)) * Φ ρ := by
  set z : ℂ := ((-a : ℝ):ℂ) + ((-T:ℝ):ℂ) * Complex.I with hz
  set w : ℂ := ((1+a : ℝ):ℂ) + ((T:ℝ):ℂ) * Complex.I with hw
  have hzre : z.re = -a := by rw [hz]; simp
  have hzim : z.im = -T := by rw [hz]; simp
  have hwre : w.re = 1+a := by rw [hw]; simp
  have hwim : w.im = T := by rw [hw]; simp
  have hre : z.re < w.re := by rw [hzre, hwre]; linarith
  have him : z.im < w.im := by rw [hzim, hwim]; linarith
  -- the boundary is zero-free
  have hbound : ∀ ζ ∈ rectangleBoundary z w, completedDedekindZetaEntire K ζ ≠ 0 := by
    intro ζ hζ
    rw [rectangleBoundary] at hζ
    rcases hζ with hζ | hζ <;> rw [Complex.mem_reProdIm] at hζ
    · -- horizontal edges
      obtain ⟨hζre, hζim⟩ := hζ
      rw [hzre, hwre, Set.uIcc_of_le (by linarith : -a ≤ 1+a), Set.mem_Icc] at hζre
      have hζeq : ζ = ((ζ.re : ℝ):ℂ) + ((ζ.im : ℝ):ℂ) * Complex.I := by
        rw [Complex.re_add_im]
      rcases hζim with h | h
      · -- bottom: im = -T
        rw [hzim] at h
        have := hbot ζ.re hζre.1 hζre.2
        rw [← h] at this
        rw [hζeq]
        exact this
      · -- top: im = T
        rw [hwim] at h
        have := htop ζ.re hζre.1 hζre.2
        rw [← h] at this
        rw [hζeq]
        exact this
    · -- vertical edges
      obtain ⟨hζre, _⟩ := hζ
      rcases hζre with h | h
      · rw [hzre] at h
        refine completedDedekindZetaEntire_ne_zero_of_re_lt_zero K ?_
        rw [h]
        linarith
      · rw [hwre] at h
        refine completedDedekindZetaEntire_ne_zero_of_one_lt_re K ?_
        rw [h]
        linarith
  -- witness in the enlarged rectangle
  have hw₀mem : ((1+a : ℝ) : ℂ) ∈ Set.Ioo (z.re - 1) (w.re + 1) ×ℂ Set.Ioo (z.im - 1) (w.im + 1) := by
    rw [Complex.mem_reProdIm, hzre, hwre, hzim, hwim]
    constructor
    · rw [Set.mem_Ioo]
      have h : (((1+a : ℝ) : ℂ)).re = 1 + a := by simp
      rw [h]
      constructor <;> linarith
    · rw [Set.mem_Ioo]
      have h : (((1+a : ℝ) : ℂ)).im = 0 := by simp
      rw [h]
      constructor <;> linarith
  have hHw₀ : completedDedekindZetaEntire K ((1+a : ℝ) : ℂ) ≠ 0 := by
    refine completedDedekindZetaEntire_ne_zero_of_one_lt_re K ?_
    simp
    linarith
  have hΦ' : ∀ ζ ∈ Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im, DifferentiableAt ℂ Φ ζ := by
    intro ζ hζ
    rw [hzre, hwre, hzim, hwim] at hζ
    exact hΦ ζ hζ
  have hmain := rectangleIntegral_mul_logDeriv_H K hre him hΦ' hbound hw₀mem hHw₀
  rw [hmain, hzre, hwre, hzim, hwim]

/-- The functional equation makes the logarithmic derivative of `H` antisymmetric
about `s = 1/2`: `H'/H(1-s) = -(H'/H)(s)`. -/
theorem logDeriv_completedDedekindZetaEntire_one_sub (s : ℂ) :
    logDeriv (completedDedekindZetaEntire K) (1 - s)
      = -(logDeriv (completedDedekindZetaEntire K) s) := by
  have hfun : (fun z : ℂ => completedDedekindZetaEntire K (1 - z))
      = completedDedekindZetaEntire K :=
    funext (completedDedekindZetaEntire_one_sub K)
  have hderiv : deriv (completedDedekindZetaEntire K) (1 - s)
      = -(deriv (completedDedekindZetaEntire K) s) := by
    have h1 : deriv (fun z : ℂ => completedDedekindZetaEntire K (1 - z)) s
        = -(deriv (completedDedekindZetaEntire K) (1 - s)) :=
      deriv_comp_const_sub (completedDedekindZetaEntire K) 1 s
    rw [hfun] at h1
    linear_combination h1
  rw [logDeriv_apply, logDeriv_apply, hderiv,
    completedDedekindZetaEntire_one_sub K s]
  rw [neg_div]

/-- **Vertical-edge folding** (SP2-RECT R-g, step 2): by the functional equation, the
two vertical edges of the contour integral combine into a single integral over the
right edge `Re = 1+a` against `Φ(s) + Φ(1-s)` — Poitou's `I(T)` shape (p. 6-02). -/
theorem rectangleIntegral_fold_vertical {a T : ℝ} (ha : 0 < a) (hT : 0 < T)
    {Φ : ℂ → ℂ} (hΦc : ContinuousOn Φ (Set.uIcc (-a) (1+a) ×ℂ Set.uIcc (-T) T)) :
    rectangleIntegral (fun ζ => Φ ζ * logDeriv (completedDedekindZetaEntire K) ζ)
        (((-a : ℝ):ℂ) + ((-T:ℝ):ℂ) * Complex.I) (((1+a : ℝ):ℂ) + ((T:ℝ):ℂ) * Complex.I)
      = (∫ x : ℝ in (-a)..(1+a),
            Φ ((x:ℂ) + ((-T:ℝ):ℂ) * Complex.I)
              * logDeriv (completedDedekindZetaEntire K) ((x:ℂ) + ((-T:ℝ):ℂ) * Complex.I))
        - (∫ x : ℝ in (-a)..(1+a),
            Φ ((x:ℂ) + ((T:ℝ):ℂ) * Complex.I)
              * logDeriv (completedDedekindZetaEntire K) ((x:ℂ) + ((T:ℝ):ℂ) * Complex.I))
        + Complex.I • ∫ y : ℝ in (-T)..T,
            (Φ (((1+a:ℝ):ℂ) + (y:ℂ) * Complex.I)
              + Φ (1 - (((1+a:ℝ):ℂ) + (y:ℂ) * Complex.I)))
              * logDeriv (completedDedekindZetaEntire K)
                  (((1+a:ℝ):ℂ) + (y:ℂ) * Complex.I) := by
  set z : ℂ := ((-a : ℝ):ℂ) + ((-T:ℝ):ℂ) * Complex.I with hz
  set w : ℂ := ((1+a : ℝ):ℂ) + ((T:ℝ):ℂ) * Complex.I with hw
  have hzre : z.re = -a := by rw [hz]; simp
  have hzim : z.im = -T := by rw [hz]; simp
  have hwre : w.re = 1+a := by rw [hw]; simp
  have hwim : w.im = T := by rw [hw]; simp
  rw [rectangleIntegral, hzre, hzim, hwre, hwim]
  -- identify the four segment integrals; only the vertical pair needs work
  -- the left edge, reflected through s ↦ 1-s and y ↦ -y, lands on the right edge
  have hleft : (∫ y : ℝ in (-T)..T,
      (fun ζ => Φ ζ * logDeriv (completedDedekindZetaEntire K) ζ)
        (((-a:ℝ):ℂ) + (y:ℂ) * Complex.I))
      = -∫ y : ℝ in (-T)..T,
          Φ (1 - (((1+a:ℝ):ℂ) + (y:ℂ) * Complex.I))
            * logDeriv (completedDedekindZetaEntire K)
                (((1+a:ℝ):ℂ) + (y:ℂ) * Complex.I) := by
    have hcomp := intervalIntegral.integral_comp_neg (a := -T) (b := T)
      (f := fun y' : ℝ => Φ (((-a:ℝ):ℂ) + ((y':ℝ):ℂ) * Complex.I)
        * logDeriv (completedDedekindZetaEntire K) (((-a:ℝ):ℂ) + ((y':ℝ):ℂ) * Complex.I))
    simp only [neg_neg] at hcomp
    rw [← hcomp]
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr (fun y hy => ?_)
    have hpt : ((-a:ℝ):ℂ) + ((-y:ℝ):ℂ) * Complex.I
        = 1 - (((1+a:ℝ):ℂ) + (y:ℂ) * Complex.I) := by
      push_cast
      ring
    rw [hpt, logDeriv_completedDedekindZetaEntire_one_sub K]
    ring
  rw [hleft]
  -- combine the two vertical integrals
  have hHne : ∀ y : ℝ, completedDedekindZetaEntire K (((1+a:ℝ):ℂ) + (y:ℂ) * Complex.I) ≠ 0 := by
    intro y
    refine completedDedekindZetaEntire_ne_zero_of_one_lt_re K ?_
    simp
    linarith
  have hld_cont : ContinuousOn
      (fun y : ℝ => logDeriv (completedDedekindZetaEntire K)
        (((1+a:ℝ):ℂ) + (y:ℂ) * Complex.I)) (Set.uIcc (-T) T) := by
    have h1 : (fun y : ℝ => logDeriv (completedDedekindZetaEntire K)
        (((1+a:ℝ):ℂ) + (y:ℂ) * Complex.I))
        = fun y : ℝ => deriv (completedDedekindZetaEntire K)
            (((1+a:ℝ):ℂ) + (y:ℂ) * Complex.I)
          / completedDedekindZetaEntire K (((1+a:ℝ):ℂ) + (y:ℂ) * Complex.I) := rfl
    rw [h1]
    refine ContinuousOn.div ?_ ?_ (fun y _ => hHne y)
    · refine Continuous.continuousOn ?_
      have hda : Continuous (deriv (completedDedekindZetaEntire K)) := by
        refine continuous_iff_continuousAt.mpr (fun ζ => ?_)
        exact ((analyticAt_completedDedekindZetaEntire K ζ).deriv).continuousAt
      exact hda.comp (by fun_prop)
    · refine Continuous.continuousOn ?_
      exact (differentiable_completedDedekindZetaEntire K).continuous.comp (by fun_prop)
  -- edge continuity of the two Φ-factors
  have hpath : Continuous (fun y : ℝ => ((1+a:ℝ):ℂ) + (y:ℂ) * Complex.I) := by fun_prop
  have hΦ_right : ContinuousOn (fun y : ℝ => Φ (((1+a:ℝ):ℂ) + (y:ℂ) * Complex.I))
      (Set.uIcc (-T) T) := by
    refine hΦc.comp hpath.continuousOn (fun y hy => ?_)
    rw [Complex.mem_reProdIm]
    constructor
    · have : (((1+a:ℝ):ℂ) + (y:ℂ) * Complex.I).re = 1+a := by simp
      rw [this]
      exact Set.right_mem_uIcc
    · have : (((1+a:ℝ):ℂ) + (y:ℂ) * Complex.I).im = y := by simp
      rw [this]
      exact hy
  have hΦ_left : ContinuousOn (fun y : ℝ => Φ (1 - (((1+a:ℝ):ℂ) + (y:ℂ) * Complex.I)))
      (Set.uIcc (-T) T) := by
    have hpath2 : Continuous (fun y : ℝ => 1 - (((1+a:ℝ):ℂ) + (y:ℂ) * Complex.I)) := by
      fun_prop
    refine hΦc.comp hpath2.continuousOn (fun y hy => ?_)
    rw [Complex.mem_reProdIm]
    constructor
    · have : (1 - (((1+a:ℝ):ℂ) + (y:ℂ) * Complex.I)).re = -a := by
        simp
      rw [this]
      exact Set.left_mem_uIcc
    · have : (1 - (((1+a:ℝ):ℂ) + (y:ℂ) * Complex.I)).im = -y := by simp
      rw [this]
      rw [Set.uIcc_of_le (by linarith : -T ≤ T), Set.mem_Icc] at hy ⊢
      constructor <;> linarith [hy.1, hy.2]
  -- combine
  have hint1 : IntervalIntegrable (fun y : ℝ =>
      Φ (((1+a:ℝ):ℂ) + (y:ℂ) * Complex.I)
        * logDeriv (completedDedekindZetaEntire K) (((1+a:ℝ):ℂ) + (y:ℂ) * Complex.I))
      volume (-T) T :=
    (hΦ_right.mul hld_cont).intervalIntegrable
  have hint2 : IntervalIntegrable (fun y : ℝ =>
      Φ (1 - (((1+a:ℝ):ℂ) + (y:ℂ) * Complex.I))
        * logDeriv (completedDedekindZetaEntire K) (((1+a:ℝ):ℂ) + (y:ℂ) * Complex.I))
      volume (-T) T :=
    (hΦ_left.mul hld_cont).intervalIntegrable
  have hsum : (∫ y : ℝ in (-T)..T,
      (Φ (((1+a:ℝ):ℂ) + (y:ℂ) * Complex.I)
        + Φ (1 - (((1+a:ℝ):ℂ) + (y:ℂ) * Complex.I)))
        * logDeriv (completedDedekindZetaEntire K) (((1+a:ℝ):ℂ) + (y:ℂ) * Complex.I))
      = (∫ y : ℝ in (-T)..T,
          Φ (((1+a:ℝ):ℂ) + (y:ℂ) * Complex.I)
            * logDeriv (completedDedekindZetaEntire K) (((1+a:ℝ):ℂ) + (y:ℂ) * Complex.I))
        + ∫ y : ℝ in (-T)..T,
            Φ (1 - (((1+a:ℝ):ℂ) + (y:ℂ) * Complex.I))
              * logDeriv (completedDedekindZetaEntire K)
                (((1+a:ℝ):ℂ) + (y:ℂ) * Complex.I) := by
    rw [← intervalIntegral.integral_add hint1 hint2]
    refine intervalIntegral.integral_congr (fun y hy => ?_)
    ring
  rw [hsum, smul_add]
  ring

/-- **Poitou's Proposition 1, quantitative form** (SP2-RECT R-g, step 3): on the
contour rectangle `[-a, 1+a] × [-T, T]` with zero-free horizontal edges, the captured
zero sum differs from the folded right-edge integral by at most the horizontal-edge
contribution `2(1+2a)·C_Φ·C_l`:

`‖2πi·∑_ρ m_ρ Φ(ρ) − i∫_{-T}^{T} (Φ+Φ(1-·))·H'/H((1+a)+iy) dy‖ ≤ 2(1+2a)·C_Φ·C_l`.

As `T → ∞` through contour heights, `C_Φ = O(1/T)` (transform decay) and
`C_l = O(log² T)` make the right side vanish — Poitou's `≡` modulo `o(1)`. -/
theorem zero_capture_edge_form {a T : ℝ} (ha : 0 < a) (ha' : a ≤ 1/4) (hT : 0 < T)
    {Φ : ℂ → ℂ}
    (hΦ : ∀ ζ ∈ Set.uIcc (-a) (1+a) ×ℂ Set.uIcc (-T) T, DifferentiableAt ℂ Φ ζ)
    (htop : ∀ σ : ℝ, -a ≤ σ → σ ≤ 1+a →
      completedDedekindZetaEntire K ((σ:ℂ) + (T:ℂ) * Complex.I) ≠ 0)
    (hbot : ∀ σ : ℝ, -a ≤ σ → σ ≤ 1+a →
      completedDedekindZetaEntire K ((σ:ℂ) + ((-T:ℝ):ℂ) * Complex.I) ≠ 0)
    {CΦ Cl : ℝ} (hCΦ0 : 0 ≤ CΦ)
    (hΦtop : ∀ x ∈ Set.uIcc (-a) (1+a), ‖Φ ((x:ℂ) + (T:ℂ) * Complex.I)‖ ≤ CΦ)
    (hΦbot : ∀ x ∈ Set.uIcc (-a) (1+a), ‖Φ ((x:ℂ) + ((-T:ℝ):ℂ) * Complex.I)‖ ≤ CΦ)
    (hltop : ∀ x ∈ Set.uIcc (-a) (1+a),
      ‖logDeriv (completedDedekindZetaEntire K) ((x:ℂ) + (T:ℂ) * Complex.I)‖ ≤ Cl)
    (hlbot : ∀ x ∈ Set.uIcc (-a) (1+a),
      ‖logDeriv (completedDedekindZetaEntire K) ((x:ℂ) + ((-T:ℝ):ℂ) * Complex.I)‖ ≤ Cl) :
    ‖2 * Real.pi * Complex.I
        * ∑ᶠ ρ, (((MeromorphicOn.divisor (completedDedekindZetaEntire K)
            (Set.Ioo (-a) (1+a) ×ℂ Set.Ioo (-T) T)) ρ : ℂ)) * Φ ρ
      - Complex.I • ∫ y : ℝ in (-T)..T,
          (Φ (((1+a:ℝ):ℂ) + (y:ℂ) * Complex.I)
            + Φ (1 - (((1+a:ℝ):ℂ) + (y:ℂ) * Complex.I)))
            * logDeriv (completedDedekindZetaEntire K)
                (((1+a:ℝ):ℂ) + (y:ℂ) * Complex.I)‖
      ≤ 2 * (1 + 2*a) * (CΦ * Cl) := by
  have hΦc : ContinuousOn Φ (Set.uIcc (-a) (1+a) ×ℂ Set.uIcc (-T) T) :=
    fun ζ hζ => (hΦ ζ hζ).continuousAt.continuousWithinAt
  have hcap := rectangle_zero_capture K ha ha' hT hΦ htop hbot
  have hfold := rectangleIntegral_fold_vertical K ha hT hΦc
  -- the difference is exactly bottom − top
  have hdiff : 2 * Real.pi * Complex.I
        * ∑ᶠ ρ, (((MeromorphicOn.divisor (completedDedekindZetaEntire K)
            (Set.Ioo (-a) (1+a) ×ℂ Set.Ioo (-T) T)) ρ : ℂ)) * Φ ρ
      - Complex.I • (∫ y : ℝ in (-T)..T,
          (Φ (((1+a:ℝ):ℂ) + (y:ℂ) * Complex.I)
            + Φ (1 - (((1+a:ℝ):ℂ) + (y:ℂ) * Complex.I)))
            * logDeriv (completedDedekindZetaEntire K)
                (((1+a:ℝ):ℂ) + (y:ℂ) * Complex.I))
      = (∫ x : ℝ in (-a)..(1+a),
            Φ ((x:ℂ) + ((-T:ℝ):ℂ) * Complex.I)
              * logDeriv (completedDedekindZetaEntire K) ((x:ℂ) + ((-T:ℝ):ℂ) * Complex.I))
        - (∫ x : ℝ in (-a)..(1+a),
            Φ ((x:ℂ) + ((T:ℝ):ℂ) * Complex.I)
              * logDeriv (completedDedekindZetaEntire K) ((x:ℂ) + ((T:ℝ):ℂ) * Complex.I)) := by
    rw [← hcap, hfold]
    ring
  rw [hdiff]
  -- bound the two horizontal edges
  have hbotb : ‖∫ x : ℝ in (-a)..(1+a),
      Φ ((x:ℂ) + ((-T:ℝ):ℂ) * Complex.I)
        * logDeriv (completedDedekindZetaEntire K) ((x:ℂ) + ((-T:ℝ):ℂ) * Complex.I)‖
      ≤ CΦ * Cl * (1 + 2*a) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (C := CΦ * Cl) (a := (-a : ℝ)) (b := (1+a : ℝ))
      (f := fun x : ℝ => Φ ((x:ℂ) + ((-T:ℝ):ℂ) * Complex.I)
        * logDeriv (completedDedekindZetaEntire K) ((x:ℂ) + ((-T:ℝ):ℂ) * Complex.I))
      (fun x hx => by
        have hx' : x ∈ Set.uIcc (-a) (1+a) := Set.uIoc_subset_uIcc hx
        rw [norm_mul]
        exact mul_le_mul (hΦbot x hx') (hlbot x hx') (norm_nonneg _) hCΦ0)
    refine le_trans this (le_of_eq ?_)
    rw [abs_of_pos (by linarith : (0:ℝ) < 1+a - -a)]
    ring
  have htopb : ‖∫ x : ℝ in (-a)..(1+a),
      Φ ((x:ℂ) + ((T:ℝ):ℂ) * Complex.I)
        * logDeriv (completedDedekindZetaEntire K) ((x:ℂ) + ((T:ℝ):ℂ) * Complex.I)‖
      ≤ CΦ * Cl * (1 + 2*a) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (C := CΦ * Cl) (a := (-a : ℝ)) (b := (1+a : ℝ))
      (f := fun x : ℝ => Φ ((x:ℂ) + ((T:ℝ):ℂ) * Complex.I)
        * logDeriv (completedDedekindZetaEntire K) ((x:ℂ) + ((T:ℝ):ℂ) * Complex.I))
      (fun x hx => by
        have hx' : x ∈ Set.uIcc (-a) (1+a) := Set.uIoc_subset_uIcc hx
        rw [norm_mul]
        exact mul_le_mul (hΦtop x hx') (hltop x hx') (norm_nonneg _) hCΦ0)
    refine le_trans this (le_of_eq ?_)
    rw [abs_of_pos (by linarith : (0:ℝ) < 1+a - -a)]
    ring
  calc ‖(∫ x : ℝ in (-a)..(1+a),
        Φ ((x:ℂ) + ((-T:ℝ):ℂ) * Complex.I)
          * logDeriv (completedDedekindZetaEntire K) ((x:ℂ) + ((-T:ℝ):ℂ) * Complex.I))
      - ∫ x : ℝ in (-a)..(1+a),
          Φ ((x:ℂ) + ((T:ℝ):ℂ) * Complex.I)
            * logDeriv (completedDedekindZetaEntire K) ((x:ℂ) + ((T:ℝ):ℂ) * Complex.I)‖
      ≤ ‖∫ x : ℝ in (-a)..(1+a),
          Φ ((x:ℂ) + ((-T:ℝ):ℂ) * Complex.I)
            * logDeriv (completedDedekindZetaEntire K) ((x:ℂ) + ((-T:ℝ):ℂ) * Complex.I)‖
        + ‖∫ x : ℝ in (-a)..(1+a),
            Φ ((x:ℂ) + ((T:ℝ):ℂ) * Complex.I)
              * logDeriv (completedDedekindZetaEntire K) ((x:ℂ) + ((T:ℝ):ℂ) * Complex.I)‖ :=
        norm_sub_le _ _
    _ ≤ CΦ * Cl * (1 + 2*a) + CΦ * Cl * (1 + 2*a) := add_le_add hbotb htopb
    _ = 2 * (1 + 2*a) * (CΦ * Cl) := by ring

end DedekindResidue

end
