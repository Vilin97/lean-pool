/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.CanonicalProductLogDerivative
public import LeanPool.Odlyzko.ECanonicalDecomposition

/-!
# Canonical Analytic Factorization

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex Filter Function MeromorphicOn Metric Set
open scoped Topology

namespace NumberField.Odlyzko

open Classical in
theorem divisor_eq_zero_of_analyticOnNhd_of_ne_zero
    {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hne : ∀ z ∈ U, f z ≠ 0) :
    MeromorphicOn.divisor f U = 0 := by
  ext z
  by_cases hz : z ∈ U
  · rw [MeromorphicOn.divisor_apply hf.meromorphicOn hz,
      (hf z hz).meromorphicOrderAt_eq,
      (hf z hz).analyticOrderAt_eq_zero.mpr (hne z hz)]
    simp
  · simp [hz]

open Classical in
theorem divisor_ball_support_subset
    {f : ℂ → ℂ} {c : ℂ} {R : ℝ} :
    (MeromorphicOn.divisor f (ball c R)).support ⊆ ball c R := by
  intro z hz
  by_contra hzball
  simp_all

open Classical in
theorem divisor_ball_eq_divisor_closedBall_of_boundary_ne
    {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hboundary : ∀ z ∈ sphere c R, f z ≠ 0) :
    ∀ z,
      MeromorphicOn.divisor f (ball c R) z =
        MeromorphicOn.divisor f (closedBall c R) z := by
  intro z
  by_cases hzball : z ∈ ball c R
  · rw [MeromorphicOn.divisor_apply
        (hf.mono ball_subset_closedBall).meromorphicOn hzball,
      MeromorphicOn.divisor_apply hf.meromorphicOn
        (ball_subset_closedBall hzball)]
  · by_cases hzclosed : z ∈ closedBall c R
    · have hzsphere : z ∈ sphere c R := by
        rw [mem_sphere, mem_closedBall, mem_ball] at *
        grind
      have hzorder :
          meromorphicOrderAt f z = 0 := by
        rw [(hf z hzclosed).meromorphicOrderAt_eq,
          (hf z hzclosed).analyticOrderAt_eq_zero.mpr
            (hboundary z hzsphere)]
        simp
      rw [MeromorphicOn.divisor_apply hf.meromorphicOn hzclosed,
        hzorder]
      simp [MeromorphicOn.divisor, hzball]
    · simp [MeromorphicOn.divisor, hzball, hzclosed]

open Classical in
theorem AnalyticOnNhd.exists_canonicalZeroFactor_on_ball_zero
    {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hc : f 0 ≠ 0)
    (hboundary : ∀ z ∈ sphere 0 R, f z ≠ 0) :
    ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (closedBall 0 R) ∧
      (∀ z ∈ closedBall 0 R, g z ≠ 0) ∧
      EqOn f
        ((centeredCanonicalZeroProduct 0 R
          (MeromorphicOn.divisor f (ball 0 R))) * g)
        (closedBall 0 R) ∧
      (∀ z ∈ sphere 0 R, ‖g z‖ = ‖f z‖) ∧
      ‖f 0‖ ≤ ‖g 0‖ := by
  let U := closedBall (0 : ℂ) R
  let D := MeromorphicOn.divisor f (ball 0 R)
  let B := centeredCanonicalZeroProduct 0 R D
  have hfmer : MeromorphicOn f U := hf.meromorphicOn
  have h0U : (0 : ℂ) ∈ U := mem_closedBall_self hR.le
  have h0ord : meromorphicOrderAt f 0 ≠ ⊤ := by
    intro htop
    have hne : f =ᶠ[𝓝[≠] 0] 0 := meromorphicOrderAt_eq_top_iff.mp htop
    have hnhds : f =ᶠ[𝓝 0] 0 :=
      ((hf 0 h0U).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
        continuousAt_const).1 hne
    exact hc hnhds.eq_of_nhds
  have hord : ∀ z : U, meromorphicOrderAt f z ≠ ⊤ := by
    intro z
    exact hfmer.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_closedBall 0 R).isPreconnected h0U z.property h0ord
  obtain ⟨g, hg⟩ := hfmer.exists_ecanonicalDecomp hord
  have hsphere :
      MeromorphicOn.divisor f (sphere 0 R) = 0 :=
    divisor_eq_zero_of_analyticOnNhd_of_ne_zero
      (hf.mono sphere_subset_closedBall) hboundary
  have hDfin : D.support.Finite := by
    exact hfmer.divisor_ball_support_finite
  have hDnonneg : ∀ z, 0 ≤ D z := by
    intro z
    exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg
      (hf.mono ball_subset_closedBall) z
  have hDinside : ∀ z ∈ D.support, z ∈ ball 0 R := by
    exact divisor_ball_support_subset
  have hBanalytic : AnalyticOnNhd ℂ B U := by
    exact analyticOnNhd_centeredCanonicalZeroProduct hDnonneg hDinside
  have hcanonical :
      (∏ᶠ u, canonicalFactor R u ^
        (-MeromorphicOn.divisor f (ball 0 R) u)) = B := by
    apply finprod_congr
    intro u
    funext z
    simp [D, centeredCanonicalZeroFactor, canonicalZeroFactor]
  have hevent : f =ᶠ[codiscreteWithin U] B * g := by
    filter_upwards [hg.eventuallyEq] with z hz
    simp_all
  have heq : EqOn f (B * g) U := by
    intro z hz
    have hprod : MeromorphicAt (B * g) z :=
      (hBanalytic z hz).meromorphicAt.mul
        (hg.analyticOnNhd z hz).meromorphicAt
    have hne : f =ᶠ[𝓝[≠] z] B * g :=
      (hfmer z hz).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
        (U := U) hprod hz (by
          dsimp [U]
          rw [← closure_ball (0 : ℂ) hR.ne']
          exact isOpen_ball.perfect_closure.2) hevent
    have hnhds : f =ᶠ[𝓝 z] B * g :=
      ((hf z hz).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
        ((hBanalytic.mul hg.analyticOnNhd) z hz).continuousAt).1 hne
    exact hnhds.eq_of_nhds
  refine ⟨g, hg.analyticOnNhd, hg.ne_zero, ?_, ?_, ?_⟩
  · grind
  · intro z hz
    have hzU : z ∈ U := sphere_subset_closedBall hz
    have heqz := heq hzU
    have hBnorm : ‖B z‖ = 1 :=
      norm_centeredCanonicalZeroProduct_eq_one hDfin hDinside hz
    simp_all
  · have heq0 := heq h0U
    have hB0 :
        ‖B 0‖ ≤ 1 :=
      norm_centeredCanonicalZeroProduct_le_one
        hDfin hDnonneg hR hDinside h0U
    simp_all

end NumberField.Odlyzko
