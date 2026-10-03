/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.RockafellarCluster.Exposed

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Supporting balls in the Straszewicz argument

This module contains the elementary Hilbert-space geometry used in Rockafellar's proof of
Straszewicz's theorem: a point of a set which is farthest from a center is exposed by the
supporting hyperplane to the corresponding closed ball.
-/

@[expose] public noncomputable section

namespace AleksandrovDifferentiability

open scoped Gradient Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- A farthest point from a sufficiently shifted center lies outside the separating halfspace.

This is the Pythagorean calculation in Rockafellar's proof of Straszewicz's theorem. The center is
`x - lam • normal`, where `x` is outside the halfspace `{z | inner normal z ≤ u}`. If all points of
`s` are close enough to `x`, then any point at least as far from this shifted center as `x` cannot
belong to that halfspace. -/
theorem inner_lt_of_norm_sub_center_le_of_forall_norm_sub_sq_lt
    {s : Set E} {normal x p : E} {u lam : ℝ}
    (hlam : 0 < lam)
    (hp : p ∈ s)
    (hbound : ∀ ⦃z : E⦄, z ∈ s → ‖z - x‖ ^ 2 < 2 * lam * (inner ℝ normal x - u))
    (hfar : ‖x - (x - lam • normal)‖ ≤ ‖p - (x - lam • normal)‖) :
    u < inner ℝ normal p := by
  by_contra hnot
  have hp_le : inner ℝ normal p ≤ u := le_of_not_gt hnot
  have hsq_le :
      ‖x - (x - lam • normal)‖ ^ 2 ≤ ‖p - (x - lam • normal)‖ ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_nonneg (norm_nonneg _)] using hfar
  have hx_center : x - (x - lam • normal) = lam • normal := by
    abel
  have hp_center : p - (x - lam • normal) = (p - x) + lam • normal := by
    abel
  have hsq_nonneg :
      0 ≤ ‖p - x‖ ^ 2 + 2 * lam * inner ℝ (p - x) normal := by
    rw [hx_center, hp_center, norm_add_sq_real, real_inner_smul_right] at hsq_le
    nlinarith
  have hinner_le : inner ℝ (p - x) normal ≤ u - inner ℝ normal x := by
    calc
      inner ℝ (p - x) normal = inner ℝ normal (p - x) := by rw [real_inner_comm]
      _ = inner ℝ normal p - inner ℝ normal x := by rw [inner_sub_right]
      _ ≤ u - inner ℝ normal x := sub_le_sub_right hp_le _
  have hterm_le :
      2 * lam * inner ℝ (p - x) normal ≤ 2 * lam * (u - inner ℝ normal x) := by
    exact mul_le_mul_of_nonneg_left hinner_le (by nlinarith)
  have hforced : 2 * lam * (inner ℝ normal x - u) ≤ ‖p - x‖ ^ 2 := by
    nlinarith
  have hcontr := hbound hp
  nlinarith

omit [CompleteSpace E] in
/-- If a set lies in the closed ball centered at `y` with `p` on the boundary, then
the supporting hyperplane to that ball at `p` exposes `p` in the set.

This is the final geometric step in Rockafellar's proof of Straszewicz's theorem: once `p` is
chosen to maximize `z ↦ ‖z - y‖` on `s`, the normal `p - y` strictly maximizes
`z ↦ inner ℝ (p - y) z` at `p`. -/
theorem exposesPoint_of_subset_closedBall
    {s : Set E} {y p : E}
    (hp : p ∈ s)
    (hsub : s ⊆ Metric.closedBall y ‖p - y‖) :
    ExposesPoint s (p - y) p := by
  refine ⟨hp, ?_⟩
  intro r hr hne
  have hdist : ‖r - y‖ ≤ ‖p - y‖ := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hsub hr
  have hsq : ‖r - y‖ ^ 2 ≤ ‖p - y‖ ^ 2 := by
    nlinarith [hdist, norm_nonneg (r - y), norm_nonneg (p - y)]
  have hdecomp : r - y = (r - p) + (p - y) := by
    abel
  have hexpand :
      ‖r - y‖ ^ 2 =
        ‖r - p‖ ^ 2 + 2 * inner ℝ (r - p) (p - y) + ‖p - y‖ ^ 2 := by
    calc
      ‖r - y‖ ^ 2 = ‖(r - p) + (p - y)‖ ^ 2 := by rw [hdecomp]
      _ = ‖r - p‖ ^ 2 + 2 * inner ℝ (r - p) (p - y) + ‖p - y‖ ^ 2 := by
        rw [norm_add_sq_real]
  have hnorm_pos : 0 < ‖r - p‖ ^ 2 := by
    have hrp_ne : r - p ≠ 0 := sub_ne_zero.mpr hne
    exact sq_pos_of_pos (norm_pos_iff.mpr hrp_ne)
  have hinner_neg : inner ℝ (r - p) (p - y) < 0 := by
    nlinarith
  have hdiff :
      inner ℝ (p - y) r - inner ℝ (p - y) p =
        inner ℝ (r - p) (p - y) := by
    rw [← inner_sub_right, real_inner_comm]
  linarith

omit [CompleteSpace E] in
/-- Farthest points from a center are exposed by the corresponding supporting ball. -/
theorem exposesPoint_of_forall_norm_sub_le
    {s : Set E} {y p : E}
    (hp : p ∈ s)
    (hmax : ∀ ⦃r : E⦄, r ∈ s → ‖r - y‖ ≤ ‖p - y‖) :
    ExposesPoint s (p - y) p :=
  exposesPoint_of_subset_closedBall hp
    (by
      intro r hr
      simpa [Metric.mem_closedBall, dist_eq_norm] using hmax hr)

omit [CompleteSpace E] in
/-- If the shifted center is far enough from the halfspace, a farthest point is an exposed point
outside that halfspace.

This packages the compact choice of `p` in Rockafellar's proof, assuming the scalar `lam` has
already been chosen so that all points of `s` satisfy the required squared-distance bound from
`x`. -/
theorem exists_exposesPoint_and_inner_lt_of_forall_norm_sub_sq_lt
    {s : Set E} (hcompact : IsCompact s) {normal x : E} {u lam : ℝ}
    (hx : x ∈ s)
    (hlam : 0 < lam)
    (hbound : ∀ ⦃z : E⦄, z ∈ s → ‖z - x‖ ^ 2 < 2 * lam * (inner ℝ normal x - u)) :
    ∃ p : E,
      p ∈ s ∧ ExposesPoint s (p - (x - lam • normal)) p ∧ u < inner ℝ normal p := by
  let y : E := x - lam • normal
  obtain ⟨p, hp, hpmax⟩ :=
    hcompact.exists_isMaxOn ⟨x, hx⟩
      ((continuous_id.sub continuous_const).norm.continuousOn : ContinuousOn (fun z => ‖z - y‖) s)
  have hfar : ‖x - y‖ ≤ ‖p - y‖ :=
    (isMaxOn_iff.mp hpmax) x hx
  have hhalf : u < inner ℝ normal p :=
    inner_lt_of_norm_sub_center_le_of_forall_norm_sub_sq_lt
      (s := s) (normal := normal) (x := x) (p := p) (u := u) (lam := lam)
      hlam hp hbound (by simpa [y] using hfar)
  exact
    ⟨p, hp,
      exposesPoint_of_forall_norm_sub_le hp
        (fun {r} hr => (isMaxOn_iff.mp hpmax) r hr),
      hhalf⟩

/-- Compact supporting-ball separation: if a point of a compact set lies outside a halfspace, then
some exposed point of the set lies outside the same halfspace.

This is the Lean-facing form of the final construction in Rockafellar's proof of Straszewicz's
theorem. Choose the shifted center far enough from `x` in the opposite normal direction, maximize
distance from that center on the compact set, and use the supporting ball at the maximizer. -/
theorem exists_mathlib_exposedPoint_inner_lt_of_isCompact_of_inner_lt
    {s : Set E} (hcompact : IsCompact s) {normal x : E} {u : ℝ}
    (hx : x ∈ s)
    (hgap : u < inner ℝ normal x) :
    ∃ p : E, p ∈ Set.exposedPoints ℝ s ∧ u < inner ℝ normal p := by
  have hcont : ContinuousOn (fun z : E => ‖z - x‖ ^ 2) s := by
    fun_prop
  obtain ⟨r, hr, hrmax⟩ := hcompact.exists_isMaxOn ⟨x, hx⟩ hcont
  let M : ℝ := ‖r - x‖ ^ 2
  let gap : ℝ := inner ℝ normal x - u
  let lam : ℝ := (M + 1) / (2 * gap)
  have hgap_pos : 0 < gap := by
    dsimp [gap]
    exact sub_pos.mpr hgap
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    positivity
  have hlam : 0 < lam := by
    dsimp [lam]
    exact div_pos (by nlinarith) (by nlinarith)
  have hscale : 2 * lam * (inner ℝ normal x - u) = M + 1 := by
    have hgap_ne : inner ℝ normal x - u ≠ 0 := (sub_pos.mpr hgap).ne'
    dsimp [lam, gap]
    field_simp [hgap_ne]
  have hbound :
      ∀ ⦃z : E⦄, z ∈ s → ‖z - x‖ ^ 2 < 2 * lam * (inner ℝ normal x - u) := by
    intro z hz
    have hzle : ‖z - x‖ ^ 2 ≤ M := by
      simpa [M] using (isMaxOn_iff.mp hrmax) z hz
    nlinarith
  obtain ⟨p, _hp, hexposed, hpout⟩ :=
    exists_exposesPoint_and_inner_lt_of_forall_norm_sub_sq_lt
      (s := s) hcompact (normal := normal) (x := x) (u := u) (lam := lam)
      hx hlam hbound
  exact ⟨p, hexposed.mem_mathlib_exposedPoints, hpout⟩

omit [CompleteSpace E] in
/-- A nonempty compact set has a farthest point from `y`, and that point is exposed by the
supporting ball centered at `y`.

This packages the final choice in Rockafellar's proof of Straszewicz's theorem: after arranging
that every point of `s` lies in a suitable ball centered at `y`, choose a point maximizing
`z ↦ ‖z - y‖`; the supporting hyperplane to that ball exposes the maximizer. -/
theorem exists_exposesPoint_of_isCompact_farthest
    {s : Set E} (hcompact : IsCompact s) (hne : s.Nonempty) (y : E) :
    ∃ p : E, p ∈ s ∧ ExposesPoint s (p - y) p := by
  obtain ⟨p, hp, hpmax⟩ :=
    hcompact.exists_isMaxOn hne
      ((continuous_id.sub continuous_const).norm.continuousOn : ContinuousOn (fun z => ‖z - y‖) s)
  exact
    ⟨p, hp,
      exposesPoint_of_forall_norm_sub_le hp (fun {r} hr => (isMaxOn_iff.mp hpmax) r hr)⟩

end AleksandrovDifferentiability
