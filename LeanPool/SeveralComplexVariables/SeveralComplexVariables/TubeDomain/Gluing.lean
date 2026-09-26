/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.Normed.Module.Convex

/-!
# Gluing local analytic continuations along a convex set

Let `g` be holomorphic on an open set `U` of a complex normed space and let `L ⊆ U` be convex.
Suppose that at every point `ζ` of `L` there is a holomorphic function on the ball of radius `δ`
around `ζ` agreeing with `g` near `ζ`. Then these local continuations agree on overlaps and
define a holomorphic function on the `δ`-neighborhood of `L` agreeing with `g` near every point
of `L`. The overlap argument passes through the midpoint of two centers, which lies in `L` and
in both balls, and uses the identity theorem on a thickened segment.

References: [Scheidemann][Scheidemann2005] §6.3, proof of Theorem 6.3.1;
[Hörmander][Hormander1973] §2.5, proof of Theorem 2.5.10.

## Main results

* `eventuallyEq_of_isPreconnected`: **Propagation of local agreement along a preconnected set.** Two
  holomorphic functions on an open set that agree near one point of a preconnected subset agree near
  every point of that subset.
* `exists_glue_of_local_continuations`: **Gluing lemma.** Local holomorphic continuations of `g` on
  balls of a fixed radius around the points of a convex set `L ⊆ U` glue to a holomorphic function
  on the `δ`-neighborhood of `L` agreeing with `g` near every point of `L`.

## References

* [L. Hörmander, *An Introduction to Complex Analysis in Several Variables*][Hormander1973]
* [V. Scheidemann, *Introduction to Complex Analysis in Several Variables*][Scheidemann2005]
-/

public noncomputable section

open Set Filter Metric
open scoped Topology

namespace SeveralComplexVariables

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- **Propagation of local agreement along a preconnected set.** Two holomorphic functions
on an open set that agree near one point of a preconnected subset agree near every point of
that subset. -/
theorem eventuallyEq_of_isPreconnected {U K : Set E} (hU : IsOpen U) {g h : E → F}
    (hg : AnalyticOnNhd ℂ g U) (hh : AnalyticOnNhd ℂ h U) (hK : IsPreconnected K) (hKU : K ⊆ U)
    {a : E} (ha : a ∈ K) (hab : h =ᶠ[𝓝 a] g) {b : E} (hb : b ∈ K) : h =ᶠ[𝓝 b] g := by
  set u : Set E := {x | h =ᶠ[𝓝 x] g} with hu
  set v : Set E := {x | x ∈ U ∧ ¬ h =ᶠ[𝓝 x] g} with hv
  have huo : IsOpen u := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    exact hx.eventually_nhds
  have hvo : IsOpen v := by
    rw [isOpen_iff_forall_mem_open]
    intro x ⟨hxU, hx⟩
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU x hxU
    refine ⟨ball x r, fun y hy => ⟨hrU hy, fun hy' => hx ?_⟩, isOpen_ball, mem_ball_self hr⟩
    have heq : EqOn h g (ball x r) :=
      (hh.mono hrU).eqOn_of_preconnected_of_eventuallyEq (hg.mono hrU)
        (convex_ball x r).isPreconnected hy hy'
    exact eventuallyEq_of_mem (isOpen_ball.mem_nhds (mem_ball_self hr)) heq
  have hcover : K ⊆ u ∪ v := fun x hx => by
    by_cases h : h =ᶠ[𝓝 x] g
    · exact Or.inl h
    · exact Or.inr ⟨hKU hx, h⟩
  have hdisj : K ∩ (u ∩ v) = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro _ hxu hxv
    exact hxv.2 hxu
  rcases isPreconnected_iff_subset_of_disjoint.mp hK u v huo hvo hcover hdisj with h | h
  · exact h hb
  · exact absurd hab (h ha).2

/-- Agreement of two holomorphic functions near a point propagates along a segment inside their
common domain: if they agree near one endpoint, they agree near the other. -/
theorem eventuallyEq_of_segment_subset {U : Set E} (hU : IsOpen U) {g h : E → F}
    (hg : AnalyticOnNhd ℂ g U) (hh : AnalyticOnNhd ℂ h U) {a b : E}
    (hseg : segment ℝ a b ⊆ U) (hab : h =ᶠ[𝓝 a] g) : h =ᶠ[𝓝 b] g :=
  eventuallyEq_of_isPreconnected hU hg hh (convex_segment a b).isPreconnected hseg
    (left_mem_segment ℝ a b) hab (right_mem_segment ℝ a b)

/-- **Gluing lemma.** Local holomorphic continuations of `g` on balls of a fixed radius
around the points of a convex set `L ⊆ U` glue to a holomorphic function on the
`δ`-neighborhood of `L` agreeing with `g` near every point of `L`. -/
theorem exists_glue_of_local_continuations {U L : Set E} (hU : IsOpen U) (hL : Convex ℝ L)
    (hLU : L ⊆ U) {g : E → F} (hg : AnalyticOnNhd ℂ g U) {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ ζ ∈ L, ∃ k : E → F, AnalyticOnNhd ℂ k (ball ζ δ) ∧ k =ᶠ[𝓝 ζ] g) :
    ∃ H : E → F, AnalyticOnNhd ℂ H (⋃ ζ ∈ L, ball ζ δ) ∧ ∀ ζ ∈ L, H =ᶠ[𝓝 ζ] g := by
  classical
  choose! k hka hkg using h
  -- each local continuation agrees with `g` near every point of `L` inside its ball
  have hkL : ∀ ζ ∈ L, ∀ m ∈ L, m ∈ ball ζ δ → k ζ =ᶠ[𝓝 m] g := by
    intro ζ hζ m hm hmζ
    have hseg : segment ℝ ζ m ⊆ ball ζ δ ∩ U :=
      subset_inter ((convex_ball ζ δ).segment_subset (mem_ball_self hδ) hmζ)
        ((hL.segment_subset hζ hm).trans hLU)
    exact eventuallyEq_of_segment_subset (isOpen_ball.inter hU)
      (hg.mono inter_subset_right) ((hka ζ hζ).mono inter_subset_left) hseg (hkg ζ hζ)
  -- two local continuations agree on the intersection of their balls
  have hconsist : ∀ ζ ∈ L, ∀ ζ' ∈ L, EqOn (k ζ) (k ζ') (ball ζ δ ∩ ball ζ' δ) := by
    intro ζ hζ ζ' hζ'
    rcases (ball ζ δ ∩ ball ζ' δ).eq_empty_or_nonempty with hemp | ⟨z, hz⟩
    · rw [hemp]; exact fun _ h => h.elim
    set m : E := midpoint ℝ ζ ζ' with hm
    have hmL : m ∈ L := hL.segment_subset hζ hζ' (midpoint_mem_segment ζ ζ')
    have hdist : dist ζ ζ' < 2 * δ := by
      calc dist ζ ζ' ≤ dist ζ z + dist z ζ' := dist_triangle _ _ _
        _ < δ + δ := add_lt_add (by simpa [dist_comm] using hz.1) (mem_ball.mp hz.2)
        _ = 2 * δ := by ring
    have hmζ : m ∈ ball ζ δ := by
      rw [mem_ball, hm, dist_comm, dist_left_midpoint, Real.norm_eq_abs, abs_of_pos two_pos,
        inv_mul_lt_iff₀ two_pos]
      exact hdist
    have hmζ' : m ∈ ball ζ' δ := by
      rw [mem_ball, hm, dist_comm, dist_right_midpoint, Real.norm_eq_abs, abs_of_pos two_pos,
        inv_mul_lt_iff₀ two_pos]
      exact hdist
    have h1 : k ζ =ᶠ[𝓝 m] k ζ' :=
      (hkL ζ hζ m hmL hmζ).trans (hkL ζ' hζ' m hmL hmζ').symm
    exact ((hka ζ hζ).mono inter_subset_left).eqOn_of_preconnected_of_eventuallyEq
      ((hka ζ' hζ').mono inter_subset_right)
      ((convex_ball ζ δ).inter (convex_ball ζ' δ)).isPreconnected ⟨hmζ, hmζ'⟩ h1
  let H : E → F := fun z =>
    if hz : ∃ ζ ∈ L, z ∈ ball ζ δ then k (Classical.choose hz) z else 0
  have hH : ∀ ζ ∈ L, ∀ z ∈ ball ζ δ, H z = k ζ z := by
    intro ζ hζ z hz
    have hex : ∃ ζ ∈ L, z ∈ ball ζ δ := ⟨ζ, hζ, hz⟩
    simp only [H]
    split_ifs
    obtain ⟨hζ', hz'⟩ := Classical.choose_spec hex
    exact hconsist _ hζ' ζ hζ ⟨hz', hz⟩
  refine ⟨H, ?_, fun ζ hζ => ?_⟩
  · intro z hz
    obtain ⟨ζ, hζ, hzζ⟩ := mem_iUnion₂.mp hz
    have : H =ᶠ[𝓝 z] k ζ := eventuallyEq_of_mem (isOpen_ball.mem_nhds hzζ) fun w hw => hH ζ hζ w hw
    exact ((hka ζ hζ) z hzζ).congr this.symm
  · have : H =ᶠ[𝓝 ζ] k ζ :=
      eventuallyEq_of_mem (isOpen_ball.mem_nhds (mem_ball_self hδ)) fun w hw => hH ζ hζ w hw
    exact this.trans (hkg ζ hζ)

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
