/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Uniform exterior sphere condition

This file defines the uniform exterior sphere condition for a set `U` in
`EuclideanSpace ℝ (Fin d)`: there is a radius `R > 0` such that every boundary
point `x₀` of `U` is touched by a closed ball of radius `R` whose interior misses
`closure U`.

## Main results

* `ViscositySolns.uniformExteriorSphere_ball`: Euclidean balls satisfy the
  condition, with radius equal to their own radius.
* `ViscositySolns.UniformExteriorSphere.exists_radius_le`: the radius can be
  taken as small as desired.
* `ViscositySolns.uniformExteriorSphere_of_contDiff_levelSet`: a bounded
  sublevel set `{ρ < 0}` of a `C²` function `ρ` whose gradient does not vanish on
  the boundary satisfies the condition.

## Proof outline for level sets

On the compact boundary `‖∇ρ‖ ≥ c > 0`, and `fderiv ℝ ρ` is `Λ`-Lipschitz on a
closed ball containing the `1`-neighbourhood of `closure U`. At a boundary point
`x₀` put `y = x₀ + R • ν` with `ν = ∇ρ x₀ / ‖∇ρ x₀‖`. If `‖x - y‖ < R` then
`‖∇ρ x₀‖ ‖x - x₀‖² < 2R ⟪∇ρ x₀, x - x₀⟫`, while the first-order Taylor bound gives
`ρ x ≥ ⟪∇ρ x₀, x - x₀⟫ - Λ ‖x - x₀‖²`. For `2RΛ ≤ c` this forces `ρ x > 0`, so
`x ∉ closure U`.
-/

@[expose] public noncomputable section

open Metric Set
open scoped Gradient RealInnerProductSpace

namespace ViscositySolns

/-- Uniform exterior sphere condition. -/
def UniformExteriorSphere {d : ℕ} (U : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∃ R > 0, ∀ x₀ ∈ frontier U, ∃ y, dist x₀ y = R ∧ ∀ x ∈ closure U, R ≤ dist x y

section Radius

variable {d : ℕ} {U : Set (EuclideanSpace ℝ (Fin d))}

/-- An exterior sphere of radius `R` at `x₀` can be replaced by a smaller one of
radius `R' ∈ (0, R]` touching at the same point: shrink the centre towards `x₀`. -/
theorem exists_exteriorSphere_of_le {x₀ y : EuclideanSpace ℝ (Fin d)} {R R' : ℝ}
    (hR' : 0 < R') (hR'R : R' ≤ R) (hy : dist x₀ y = R) (hU : ∀ x ∈ U, R ≤ dist x y) :
    ∃ y', dist x₀ y' = R' ∧ ∀ x ∈ U, R' ≤ dist x y' := by
  have hR : 0 < R := hR'.trans_le hR'R
  refine ⟨x₀ + (R' / R) • (y - x₀), ?_, fun x hx => ?_⟩
  · rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, ← dist_eq_norm', hy,
      Real.norm_of_nonneg (by positivity)]
    field_simp
  · -- `dist y y' = R - R'`, then use the triangle inequality.
    have hyy' : dist y (x₀ + (R' / R) • (y - x₀)) = R - R' := by
      have : y - (x₀ + (R' / R) • (y - x₀)) = (1 - R' / R) • (y - x₀) := by
        rw [sub_smul, one_smul]; abel
      have hyx : ‖y - x₀‖ = R := by rw [← dist_eq_norm, dist_comm, hy]
      have hnn : 0 ≤ 1 - R' / R := by rw [sub_nonneg, div_le_one hR]; exact hR'R
      rw [dist_eq_norm, this, norm_smul, hyx, Real.norm_of_nonneg hnn]
      field_simp
    have := dist_triangle x (x₀ + (R' / R) • (y - x₀)) y
    linarith [hU x hx, dist_comm (x₀ + (R' / R) • (y - x₀)) y]

/-- If the uniform exterior sphere condition holds, it holds with a radius no
larger than any prescribed `R₀ > 0`. -/
theorem UniformExteriorSphere.exists_radius_le (hU : UniformExteriorSphere U) {R₀ : ℝ}
    (hR₀ : 0 < R₀) :
    ∃ R > 0, R ≤ R₀ ∧
      ∀ x₀ ∈ frontier U, ∃ y, dist x₀ y = R ∧ ∀ x ∈ closure U, R ≤ dist x y := by
  obtain ⟨R, hR, hext⟩ := hU
  refine ⟨min R R₀, lt_min hR hR₀, min_le_right _ _, fun x₀ hx₀ => ?_⟩
  obtain ⟨y, hy, hcl⟩ := hext x₀ hx₀
  exact exists_exteriorSphere_of_le (lt_min hR hR₀) (min_le_left _ _) hy hcl

end Radius

/-- A Euclidean ball satisfies the uniform exterior sphere condition with its own
radius: at `x₀` on the boundary, use the ball centred at the reflection
`x₀ + (x₀ - c)` of the centre through `x₀`. -/
theorem uniformExteriorSphere_ball {d : ℕ} (c : EuclideanSpace ℝ (Fin d)) {t : ℝ} (ht : 0 < t) :
    UniformExteriorSphere (Metric.ball c t) := by
  refine ⟨t, ht, fun x₀ hx₀ => ⟨x₀ + (x₀ - c), ?_, fun x hx => ?_⟩⟩
  · have hx₀t : dist x₀ c = t := frontier_ball_subset_sphere hx₀
    rw [dist_eq_norm, sub_add_cancel_left, norm_neg, ← dist_eq_norm, hx₀t]
  · have hx₀t : dist x₀ c = t := frontier_ball_subset_sphere hx₀
    have hxc : dist x c ≤ t := closure_ball_subset_closedBall hx
    -- The new centre is at distance `2t` from `c`.
    have hyc : dist (x₀ + (x₀ - c)) c = 2 * t := by
      have : x₀ + (x₀ - c) - c = (2 : ℝ) • (x₀ - c) := by rw [two_smul]; abel
      rw [dist_eq_norm, this, norm_smul, ← dist_eq_norm, hx₀t, Real.norm_two]
    have := dist_triangle (x₀ + (x₀ - c)) x c
    linarith [dist_comm x (x₀ + (x₀ - c))]

section LevelSet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A `C²` function has Lipschitz derivative on every convex compact set. -/
theorem exists_norm_fderiv_sub_le_of_contDiff {ρ : E → ℝ} (hρ : ContDiff ℝ 2 ρ) {K : Set E}
    (hK : IsCompact K) (hKc : Convex ℝ K) :
    ∃ Λ, 0 ≤ Λ ∧ ∀ w ∈ K, ∀ z ∈ K, ‖fderiv ℝ ρ w - fderiv ℝ ρ z‖ ≤ Λ * ‖w - z‖ := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ ρ) := hρ.fderiv_right (by norm_num)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (h1.continuous_fderiv one_ne_zero).continuousOn
  refine ⟨max C 0, le_max_right _ _, fun w hw z hz => ?_⟩
  exact hKc.norm_image_sub_le_of_norm_fderiv_le (fun x _ => h1.differentiable one_ne_zero x)
    (fun x hx => (hC x hx).trans (le_max_left _ _)) hz hw

/-- First-order Taylor lower bound: if `fderiv ℝ ρ` stays within `Λ ‖x - x₀‖` of
`fderiv ℝ ρ x₀` on the closed ball `closedBall x₀ ‖x - x₀‖`, then
`ρ x ≥ ρ x₀ + fderiv ℝ ρ x₀ (x - x₀) - Λ ‖x - x₀‖²`. -/
theorem le_of_norm_fderiv_sub_le {ρ : E → ℝ} (hρ : Differentiable ℝ ρ) {x₀ x : E} {Λ : ℝ}
    (hΛ : ∀ w ∈ closedBall x₀ ‖x - x₀‖, ‖fderiv ℝ ρ w - fderiv ℝ ρ x₀‖ ≤ Λ * ‖x - x₀‖) :
    ρ x₀ + fderiv ℝ ρ x₀ (x - x₀) - Λ * ‖x - x₀‖ ^ 2 ≤ ρ x := by
  set L := fderiv ℝ ρ x₀
  -- Mean value inequality for `z ↦ ρ z - L z` on the ball.
  have hmvt := (convex_closedBall x₀ ‖x - x₀‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun z => ρ z - L z) (f' := fun w => fderiv ℝ ρ w - L)
    (fun w _ => ((hρ w).hasFDerivAt.sub L.hasFDerivAt).hasFDerivWithinAt) hΛ
    (mem_closedBall_self (norm_nonneg _)) (by rw [mem_closedBall, dist_eq_norm])
  rw [Real.norm_eq_abs] at hmvt
  have h := (abs_le.1 hmvt).1
  rw [map_sub]
  have : Λ * ‖x - x₀‖ ^ 2 = Λ * ‖x - x₀‖ * ‖x - x₀‖ := by ring
  linarith

end LevelSet

/-- A bounded sublevel set `{ρ < 0}` of a `C²` function whose gradient does not
vanish on the boundary satisfies the uniform exterior sphere condition. -/
theorem uniformExteriorSphere_of_contDiff_levelSet {d : ℕ} {U : Set (EuclideanSpace ℝ (Fin d))}
    (hUb : Bornology.IsBounded U)
    (hC2 : ∃ ρ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ 2 ρ ∧ U = {x | ρ x < 0} ∧
      ∀ x ∈ frontier U, ∇ ρ x ≠ 0) :
    UniformExteriorSphere U := by
  obtain ⟨ρ, hρ, hUeq, hgrad⟩ := hC2
  have hρc : Continuous ρ := hρ.continuous
  have hρd : Differentiable ℝ ρ := hρ.differentiable (by norm_num)
  have hUo : IsOpen U := hUeq ▸ isOpen_lt hρc continuous_const
  -- `ρ ≤ 0` on `closure U` and `ρ ≥ 0` on `frontier U`.
  have hcl : ∀ x ∈ closure U, ρ x ≤ 0 := fun x hx =>
    closure_lt_subset_le hρc continuous_const (hUeq ▸ hx)
  have hfr : ∀ x ∈ frontier U, 0 ≤ ρ x := fun x hx => by
    rw [hUo.frontier_eq] at hx
    have : x ∉ {x | ρ x < 0} := hUeq ▸ hx.2
    simpa using this
  -- The gradient and `fderiv` have the same norm.
  have hnorm : ∀ x, ‖∇ ρ x‖ = ‖fderiv ℝ ρ x‖ := fun x => by
    simp [gradient]
  rcases (frontier U).eq_empty_or_nonempty with he | hne
  · exact ⟨1, one_pos, by simp [he]⟩
  -- Lower bound `c` for `‖∇ρ‖` on the compact frontier.
  have hfc : IsCompact (frontier U) :=
    isCompact_of_isClosed_isBounded isClosed_frontier (hUb.closure.subset frontier_subset_closure)
  obtain ⟨xm, hxm, hmin⟩ := hfc.exists_isMinOn hne
    ((hρ.continuous_fderiv (by norm_num)).norm.continuousOn)
  set c := ‖fderiv ℝ ρ xm‖ with hc_def
  have hc : 0 < c := by rw [hc_def, ← hnorm]; exact norm_pos_iff.2 (hgrad xm hxm)
  -- Lipschitz constant `Λ` for `fderiv ℝ ρ` near `closure U`.
  obtain ⟨M, hM⟩ := hUb.closure.subset_closedBall 0
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_norm_fderiv_sub_le_of_contDiff hρ
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) (M + 1)) (convex_closedBall 0 (M + 1))
  set R := min (1 / 2) (c / (2 * (Λ + 1))) with hR_def
  have hR : 0 < R := lt_min (by norm_num) (by positivity)
  have hR1 : 2 * R ≤ 1 := by linarith [min_le_left (1 / 2 : ℝ) (c / (2 * (Λ + 1)))]
  have hRΛ : 2 * R * Λ ≤ c := by
    have h1 : R ≤ c / (2 * (Λ + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  refine ⟨R, hR, fun x₀ hx₀ => ?_⟩
  set g := ∇ ρ x₀ with hg_def
  set a := ‖g‖ with ha_def
  have hca : c ≤ a := by rw [ha_def, hg_def, hnorm]; exact hmin hx₀
  have ha : 0 < a := hc.trans_le hca
  refine ⟨x₀ + (R / a) • g, ?_, fun x hx => ?_⟩
  · rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, ← ha_def,
      Real.norm_of_nonneg (by positivity)]
    field_simp
  by_contra hlt
  push Not at hlt
  set h := x - x₀ with hh_def
  set s := ⟪g, h⟫ with hs_def
  -- From `‖x - y‖ < R`: `a ‖h‖² < 2 R ⟪g, h⟫`.
  have hkey : a * ‖h‖ ^ 2 < 2 * R * s := by
    have hxy : x - (x₀ + (R / a) • g) = h - (R / a) • g := by rw [hh_def]; abel
    rw [dist_eq_norm, hxy] at hlt
    have hsq : ‖h - (R / a) • g‖ ^ 2 < R ^ 2 := by
      have := norm_nonneg (h - (R / a) • g)
      nlinarith
    rw [norm_sub_sq_real, inner_smul_right, norm_smul, ← ha_def,
      Real.norm_of_nonneg (by positivity), real_inner_comm, ← hs_def] at hsq
    have e1 : R / a * a = R := by field_simp
    rw [e1] at hsq
    have e2 : 2 * (R / a * s) = (2 * R * s) / a := by field_simp
    rw [e2] at hsq
    have : ‖h‖ ^ 2 < 2 * R * s / a := by linarith
    rwa [lt_div_iff₀ ha, mul_comm] at this
  -- `‖h‖ ≤ 1`, so the ball `closedBall x₀ ‖h‖` stays in the Lipschitz region.
  have hh1 : ‖h‖ ≤ 1 := by
    have h1 : dist x x₀ ≤ dist x (x₀ + (R / a) • g) + dist (x₀ + (R / a) • g) x₀ :=
      dist_triangle _ _ _
    have h2 : dist (x₀ + (R / a) • g) x₀ = R := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, ← ha_def,
        Real.norm_of_nonneg (by positivity)]
      field_simp
    rw [dist_eq_norm] at h1
    linarith
  have hx₀M : x₀ ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) M := hM (frontier_subset_closure hx₀)
  have hball : closedBall x₀ ‖h‖ ⊆ closedBall 0 (M + 1) := by
    intro w hw
    rw [mem_closedBall] at hw hx₀M ⊢
    linarith [dist_triangle w x₀ 0]
  have htaylor := le_of_norm_fderiv_sub_le hρd (x₀ := x₀) (x := x) (Λ := Λ) fun w hw => by
    refine (hΛ w (hball hw) x₀ (hball (mem_closedBall_self (norm_nonneg _)))).trans ?_
    exact mul_le_mul_of_nonneg_left (by rwa [mem_closedBall, dist_eq_norm] at hw) hΛ0
  have hLs : fderiv ℝ ρ x₀ h = s := by
    rw [hs_def, hg_def, inner_gradient_left]
  rw [← hh_def, hLs] at htaylor
  have hρx := hcl x hx
  have hρx₀ := hfr x₀ hx₀
  -- Combine: `a ‖h‖² < 2 R s ≤ 2 R Λ ‖h‖² ≤ c ‖h‖² ≤ a ‖h‖²`.
  have hs : 2 * R * s ≤ 2 * R * Λ * ‖h‖ ^ 2 := by
    have : s ≤ Λ * ‖h‖ ^ 2 := by linarith
    have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 2 * R)
    linarith
  have hq := sq_nonneg ‖h‖
  have h3 : 2 * R * Λ * ‖h‖ ^ 2 ≤ a * ‖h‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (hRΛ.trans hca) hq
  linarith

end ViscositySolns
