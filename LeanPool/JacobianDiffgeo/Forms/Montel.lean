/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Planar Montel theorem (holomorphic-forms unit)

This file proves **Montel's theorem** in compactness form for the complex plane, together with
the Cauchy derivative estimate feeding it. It is deliberately free of any manifold imports so
that `finiteness-and-chi` (compact-operator argument) can import it cheaply.

Main declarations:
* `RS.norm_deriv_le_of_bounded` — Cauchy estimate: `‖deriv g z‖ ≤ C / r` for `g` holomorphic and
  bounded by `C` on an open set containing `closedBall z r`.
* `RS.montelFamily Ω K C` — restrictions to a compact `K` of functions holomorphic on `Ω ⊇ K`
  and bounded by `C` there, as a subset of `C(K, ℂ)`.
* `RS.isCompact_closure_montelFamily` — the closure of `montelFamily Ω K C` is compact in
  `C(K, ℂ)` (Cauchy estimate ⇒ equicontinuity ⇒ Arzelà–Ascoli).
-/

namespace RS

open Metric Set

open scoped BoundedContinuousFunction

/-- **Cauchy estimate**: if `g` is holomorphic on an open set `Ω` and bounded by `C` there, then
its derivative at the center of any closed ball of radius `r` contained in `Ω` is bounded by
`C / r`. -/
theorem norm_deriv_le_of_bounded {Ω : Set ℂ} {g : ℂ → ℂ} {C : ℝ} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) (hC : ∀ w ∈ Ω, ‖g w‖ ≤ C) {z : ℂ} {r : ℝ}
    (hr : 0 < r) (hball : Metric.closedBall z r ⊆ Ω) : ‖deriv g z‖ ≤ C / r := by
  rw [← Complex.cderiv_eq_deriv hΩ hg hr hball]
  exact Complex.norm_cderiv_le hr fun w hw => hC w (hball (sphere_subset_closedBall hw))

/-- The set of restrictions to a compact `K` of functions holomorphic on an open `Ω ⊇ K` and
bounded by `C` there. -/
def montelFamily (Ω K : Set ℂ) (C : ℝ) : Set C(K, ℂ) :=
  {f | ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ (∀ z ∈ Ω, ‖g z‖ ≤ C) ∧ ∀ z : K, f z = g z}

/-- Interior Lipschitz estimate for a bounded holomorphic function: on the half-thickening of a
set `K` whose `δ`-thickening stays in `Ω`, `g` is `(2C/δ)`-Lipschitz. -/
theorem norm_sub_le_of_bounded_of_cthickening_subset {Ω K : Set ℂ} (hΩ : IsOpen Ω)
    {δ C : ℝ} (hδ : 0 < δ) (hsub : Metric.cthickening δ K ⊆ Ω) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g Ω) (hC : ∀ z ∈ Ω, ‖g z‖ ≤ C) {z w : ℂ} (hz : z ∈ K)
    (hw : dist w z ≤ δ / 2) : ‖g w - g z‖ ≤ 2 * C / δ * ‖w - z‖ := by
  have hδ2 : (0 : ℝ) < δ / 2 := half_pos hδ
  have hball : Metric.closedBall z δ ⊆ Ω :=
    (Metric.closedBall_subset_cthickening hz δ).trans hsub
  have hsball : Metric.closedBall z (δ / 2) ⊆ Ω :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans hball
  refine Convex.norm_image_sub_le_of_norm_deriv_le
    (fun y hy => hg.differentiableAt (hΩ.mem_nhds (hsball hy)))
    (fun y hy => ?_) (convex_closedBall z (δ / 2)) (Metric.mem_closedBall_self hδ2.le) hw
  -- derivative bound at `y ∈ closedBall z (δ/2)`
  have hyball : Metric.closedBall y (δ / 2) ⊆ Ω := by
    intro u hu
    apply hball
    have h1 : dist u z ≤ dist u y + dist y z := dist_triangle u y z
    have h2 : dist u y ≤ δ / 2 := Metric.mem_closedBall.mp hu
    have h3 : dist y z ≤ δ / 2 := Metric.mem_closedBall.mp hy
    exact Metric.mem_closedBall.mpr (by linarith)
  have hest := norm_deriv_le_of_bounded hΩ hg hC hδ2 hyball
  calc ‖deriv g y‖ ≤ C / (δ / 2) := hest
    _ = 2 * C / δ := by rw [div_div_eq_mul_div, mul_comm]

/-- **Montel's theorem**, compactness form: a family of holomorphic functions on an open
`Ω ⊇ K` with a common bound, restricted to the compact `K`, has compact closure in `C(K, ℂ)`. -/
theorem isCompact_closure_montelFamily {Ω K : Set ℂ} (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) (C : ℝ) : IsCompact (closure (montelFamily Ω K C)) := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · -- `K` empty: `C(K, ℂ)` is a subsingleton, every subset is compact.
    have : IsEmpty (↥K) := Set.isEmpty_coe_sort.mpr hKe
    have : Subsingleton C(↥K, ℂ) := ⟨fun f g => ContinuousMap.ext fun x => isEmptyElim x⟩
    exact Set.subsingleton_of_subsingleton.isCompact
  rcases lt_or_ge C 0 with hC | hC
  · -- negative bound: the family is empty.
    have hfam : montelFamily Ω K C = ∅ := by
      ext f
      simp only [montelFamily, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_exists]
      rintro g ⟨-, hbd, -⟩
      obtain ⟨z, hz⟩ := hKne
      exact absurd ((norm_nonneg (g z)).trans (hbd z (hKΩ hz))) (not_le.mpr hC)
    rw [hfam, closure_empty]
    exact isCompact_empty
  -- main case: `0 ≤ C`.
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  have hL0 : (0 : ℝ) ≤ 2 * C / δ := div_nonneg (by linarith) hδ.le
  set L : ℝ := 2 * C / δ with hLdef
  let E : C(↥K, ℂ) ≃ₜ (↥K →ᵇ ℂ) := (ContinuousMap.isometryEquivBoundedOfCompact ↥K ℂ).toHomeomorph
  have hEapp : ∀ (f : C(↥K, ℂ)) (y : ↥K), E f y = f y := fun f y => rfl
  have key : IsCompact (closure (E '' montelFamily Ω K C)) := by
    apply BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0 : ℂ) C)
      (isCompact_closedBall 0 C)
    · -- pointwise range containment
      rintro f x ⟨f₀, ⟨g, -, hbd, hfg⟩, rfl⟩
      rw [mem_closedBall_zero_iff, hEapp, hfg x]
      exact hbd x (hKΩ x.2)
    · -- equicontinuity from the interior Lipschitz estimate
      intro x₀
      rw [Metric.equicontinuousAt_iff]
      intro ε hε
      have hL1 : (0 : ℝ) < L + 1 := by linarith
      refine ⟨min (δ / 2) (ε / (L + 1)), lt_min (half_pos hδ) (div_pos hε hL1), fun x hx i => ?_⟩
      obtain ⟨f, hf⟩ := i
      obtain ⟨f₀, ⟨g, hg, hbd, hfg⟩, rfl⟩ := hf
      have hdist : dist (x : ℂ) (x₀ : ℂ) ≤ δ / 2 := by
        rw [← Subtype.dist_eq]
        exact ((lt_min_iff.mp hx).1).le
      have hlip := norm_sub_le_of_bounded_of_cthickening_subset hΩ hδ hsub hg hbd x₀.2 hdist
      have hstep : dist (g (x : ℂ)) (g (x₀ : ℂ)) ≤ L * dist x x₀ := by
        rw [dist_eq_norm, Subtype.dist_eq, dist_eq_norm]
        exact hlip
      change dist ((E f₀) x₀) ((E f₀) x) < ε
      rw [hEapp, hEapp, hfg x, hfg x₀, dist_comm]
      calc dist (g (x : ℂ)) (g (x₀ : ℂ))
          ≤ L * dist x x₀ := hstep
        _ ≤ L * (ε / (L + 1)) := by
            refine mul_le_mul_of_nonneg_left ?_ hL0
            exact (lt_of_lt_of_le hx (min_le_right _ _)).le
        _ < ε := by
            have h1 : L / (L + 1) < 1 := (div_lt_one hL1).mpr (by linarith)
            calc L * (ε / (L + 1)) = ε * (L / (L + 1)) := by ring
              _ < ε * 1 := by exact mul_lt_mul_of_pos_left h1 hε
              _ = ε := mul_one ε
  rw [← Homeomorph.image_closure] at key
  exact (Homeomorph.isCompact_image E).mp key

end RS
