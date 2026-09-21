/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic
import LeanPool.NandakumarRamanaRao.NRR.BodySpace.ConvexClosed

/-!
# Pointwise membership stability for Hausdorff-convergent convex subbodies

For a family of convex subbodies `C a → C₀` in the Hausdorff metric this module establishes the
pointwise stability of membership in the underlying carriers:

* `ConvexSubbody.mem_limit_of_tendsto` — the membership graph is closed: if `x a ∈ C a`
  eventually, `C a → C₀` and `x a → x₀`, then `x₀ ∈ C₀` (needs a `NeBot` index filter);
* `ConvexSubbody.exists_tendsto_points` — every point of a limit body is the limit of a
  sequence of points chosen from the approximating bodies;
* `ConvexSubbody.eventually_not_mem_of_not_mem` — exterior stability: a point outside the
  closed limit body is eventually outside the approximating bodies;
* `ConvexSubbody.eventually_mem_of_mem_interior` — interior stability: a point in the interior
  of the limit body is eventually inside the approximating bodies;
* `ConvexSubbody.eventually_mem_iff_of_not_mem_frontier` — off the frontier, membership in the
  approximating bodies eventually agrees with membership in the limit body.

Interior stability is the geometric heart: it rests on the strict separation of an exterior point
from a compact convex set by a unit normal, packaged as the auxiliary set lemmas
`exists_separating_unit` and `mem_of_hausdorffDist_lt`.
-/

open MeasureTheory Metric Filter Topology
open scoped RealInnerProductSpace

open NRR.Geometry

namespace NRR

namespace ConvexSubbody

variable {K : Geometry.ConvexBody Plane}

/-
**Separation of an exterior point.** A point `x` outside a nonempty compact convex set `D`
in the plane admits a unit normal `u` with `⟪y, u⟫ ≤ ⟪x, u⟫` for all `y ∈ D`.
-/
theorem exists_separating_unit {D : Set Plane} (hconv : Convex ℝ D)
    (hcomp : IsCompact D) (hne : D.Nonempty) {x : Plane} (hx : x ∉ D) :
    ∃ u : Plane, ‖u‖ = 1 ∧ ∀ y ∈ D, ⟪y, u⟫ ≤ ⟪x, u⟫ := by
  obtain ⟨ p, hp, h ⟩ := hcomp.exists_infDist_eq_dist hne x;
  refine' ⟨ ‖x - p‖⁻¹ • ( x - p ), _, _ ⟩ <;> simp_all +decide [ norm_smul, dist_eq_norm' ];
  · rw [ inv_mul_cancel₀ ( norm_ne_zero_iff.mpr ( sub_ne_zero.mpr ( by aesop ) ) ) ];
  · -- By the variational inequality for the metric projection, we have ⟪x - p, y - p⟫ ≤ 0 for all y ∈ D.
    have h_var : ∀ y ∈ D, ⟪x - p, y - p⟫ ≤ 0 := by
      convert norm_eq_iInf_iff_real_inner_le_zero hconv hp |>.1 _ using 1;
      convert h.symm using 1;
      · rw [ norm_sub_rev ];
      · rw [ Metric.infDist_eq_iInf ];
        simp +decide only [dist_eq_norm];
    simp_all +decide [ inner_sub_left, inner_sub_right, inner_smul_right ];
    intro y hy; rw [ mul_le_mul_iff_right₀ ( inv_pos.mpr ( norm_pos_iff.mpr ( sub_ne_zero.mpr <| by aesop ) ) ) ]; simp_all +decide [ real_inner_comm ];
    nlinarith [ h_var y hy, norm_nonneg ( x - p ), norm_sub_sq_real x p, real_inner_self_eq_norm_sq x, real_inner_self_eq_norm_sq p, real_inner_comm x p ]

/-
**Membership from a small Hausdorff distance.** If `x` is deep inside `E` (a closed ball of
radius `ε` around `x` is contained in `E`) and a nonempty compact convex set `D` is within
Hausdorff distance `< ε` of `E`, then `x ∈ D`.
-/
theorem mem_of_hausdorffDist_lt {D E : Set Plane} (hDconv : Convex ℝ D)
    (hDcomp : IsCompact D) (hDne : D.Nonempty)
    (hEbdd : Bornology.IsBounded E) (hEne : E.Nonempty)
    {x : Plane} {ε : ℝ} (hε : 0 < ε) (hball : Metric.closedBall x ε ⊆ E)
    (hdist : Metric.hausdorffDist D E < ε) : x ∈ D := by
  by_contra hx;
  -- By `exists_separating_unit hDconv hDcomp hDne hx`, obtain a unit vector `u` (`‖u‖ = 1`) with `∀ y ∈ D, ⟪y, u⟫ ≤ ⟪x, u⟫`.
  obtain ⟨u, hu⟩ : ∃ u : Plane, ‖u‖ = 1 ∧ ∀ y ∈ D, ⟪y, u⟫ ≤ ⟪x, u⟫ :=
    exists_separating_unit hDconv hDcomp hDne hx
  -- Let `z := x + ε • u`. Then `dist z x = ‖z - x‖ = ‖ε • u‖ = |ε| * ‖u‖ = ε`, so `z ∈ Metric.closedBall x ε`, hence `z ∈ E` by `hball`.
  set z : Plane := x + ε • u
  have hz : z ∈ E := by
    refine' hball _;
    simp only [z, Metric.mem_closedBall, dist_self_add_left]
    rw [norm_smul, Real.norm_of_nonneg hε.le, hu.1, mul_one]
  -- Since `z ∈ E`, `Metric.infDist z D ≤ Metric.hausdorffDist E D` (via `Metric.infDist_le_hausdorffDist_of_mem`, using symmetry of hausdorffEDist finiteness), and `Metric.hausdorffDist E D = Metric.hausdorffDist D E` by `Metric.hausdorffDist_comm`. So `Metric.infDist z D < ε` by `hdist`.
  have h_infDist_z_D : Metric.infDist z D < ε := by
    have h_ne_top : Metric.hausdorffEDist E D ≠ ⊤ :=
      Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded hEne hDne hEbdd hDcomp.isBounded
    have h_le := Metric.infDist_le_hausdorffDist_of_mem hz h_ne_top
    rw [Metric.hausdorffDist_comm] at h_le
    exact lt_of_le_of_lt h_le hdist
  obtain ⟨ w, hw₁, hw₂ ⟩ := hDcomp.exists_infDist_eq_dist hDne z;
  -- Compute the inner product with `u`: `⟪z - w, u⟫ = ⟪x, u⟫ + ε * ⟪u, u⟫ - ⟪w, u⟫ = ⟪x, u⟫ + ε - ⟪w, u⟫` (since `⟪u, u⟫ = ‖u‖^2 = 1`). Using `⟪w, u⟫ ≤ ⟪x, u⟫` from step 1, this gives `⟪z - w, u⟫ ≥ ε`.
  have h_inner : ⟪z - w, u⟫ ≥ ε := by
    simp +zetaDelta at *;
    simp_all +decide [ inner_add_left, inner_sub_left, inner_smul_left ];
    linarith [ hu.2 w hw₁ ];
  -- But by Cauchy–Schwarz, `⟪z - w, u⟫ ≤ ‖z - w‖ * ‖u‖ = ‖z - w‖ = dist z w < ε`. This contradicts step 6.
  have h_cauchy_schwarz : ⟪z - w, u⟫ ≤ ‖z - w‖ * ‖u‖ := by
    exact real_inner_le_norm _ _;
  simp_all +decide [ dist_eq_norm ];
  linarith

/-
**Closed membership graph.** If `x a ∈ C a` eventually, `C a → C₀` in the Hausdorff metric,
and `x a → x₀`, then `x₀ ∈ C₀`. The `NeBot` hypothesis is essential: on the bottom filter every
`∀ᶠ`/`Tendsto` hypothesis is vacuous.
-/
theorem mem_limit_of_tendsto
    {α : Type*} {l : Filter α} [NeBot l]
    {C : α → ConvexSubbody K} {C₀ : ConvexSubbody K}
    {x : α → Plane} {x₀ : Plane}
    (hC : Tendsto C l (𝓝 C₀))
    (hx : Tendsto x l (𝓝 x₀))
    (hmem : ∀ᶠ a in l, x a ∈ ((C a).body : Set Plane)) :
    x₀ ∈ (C₀.body : Set Plane) := by
  -- Since $C₀$ is closed, it suffices to show that $x₀$ is a limit point of $C₀$.
  have h_limit_point : x₀ ∈ closure (C₀.body : Set Plane) := by
    have h_limit_point : ∀ᶠ a in l, Metric.infDist (x a) (C₀.body : Set Plane) ≤ Metric.hausdorffDist (C a).body (C₀.body : Set Plane) := by
      filter_upwards [ hmem ] with a ha;
      apply_rules [ Metric.infDist_le_hausdorffDist_of_mem ];
      apply_rules [ Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded ];
      · exact ⟨ _, ha ⟩;
      · exact C₀.nonempty;
      · exact ( C a ).isCompact.isBounded;
      · exact C₀.isCompact.isBounded;
    have h_limit_point : Metric.infDist x₀ (C₀.body : Set Plane) ≤ 0 := by
      have h_limit_point : Filter.Tendsto (fun a => Metric.infDist (x a) (C₀.body : Set Plane)) l (nhds (Metric.infDist x₀ (C₀.body : Set Plane))) := by
        exact Metric.continuous_infDist_pt _ |> Continuous.continuousAt |> fun h => h.tendsto.comp hx;
      have h_limit_point : Filter.Tendsto (fun a => Metric.hausdorffDist (C a).body (C₀.body : Set Plane)) l (nhds 0) := by
        convert ConvexSubbody.tendsto_hausdorffDist_zero hC using 1;
      exact le_of_tendsto_of_tendsto ‹_› ‹_› ( by filter_upwards [ ‹∀ᶠ a in l, infDist ( x a ) ( C₀.body : Set Plane ) ≤ hausdorffDist ( C a |> ConvexSubbody.body ) ( C₀.body : Set Plane ) › ] with a ha using ha );
    rw [ Metric.mem_closure_iff_infDist_zero ];
    · exact le_antisymm h_limit_point ( Metric.infDist_nonneg );
    · exact C₀.nonempty;
  exact C₀.isCompact.isClosed.closure_subset h_limit_point

/-
**Point approximation.** Every point of a limit body `C₀` is the limit of a sequence of
points chosen from the approximating bodies `C m`.
-/
theorem exists_tendsto_points
    {C : ℕ → ConvexSubbody K} {C₀ : ConvexSubbody K}
    (hC : Tendsto C atTop (𝓝 C₀))
    {x : Plane} (hx : x ∈ (C₀.body : Set Plane)) :
    ∃ xseq : ℕ → Plane,
      (∀ m, xseq m ∈ ((C m).body : Set Plane)) ∧
      Tendsto xseq atTop (𝓝 x) :=
  BodySpace.exists_tendsto_points_of_tendsto_nonemptyCompacts (ConvexSubbody.tendsto_body hC) hx

/-
**Exterior stability.** A point outside the closed limit body is eventually outside the
approximating bodies.
-/
theorem eventually_not_mem_of_not_mem
    {α : Type*} {l : Filter α}
    {C : α → ConvexSubbody K} {C₀ : ConvexSubbody K}
    (hC : Tendsto C l (𝓝 C₀))
    {x : Plane} (hx : x ∉ (C₀.body : Set Plane)) :
    ∀ᶠ a in l, x ∉ ((C a).body : Set Plane) := by
  obtain ⟨d, hd_pos, hd⟩ : ∃ d > 0, Metric.infDist x (C₀.body : Set Plane) = d := by
    refine' ⟨ _, _, rfl ⟩;
    contrapose! hx;
    exact C₀.isCompact.isClosed.closure_subset_iff.mpr ( Set.Subset.refl _ ) ( Metric.mem_closure_iff.mpr fun ε εpos => by have := Metric.infDist_lt_iff ( C₀.nonempty ) |>.1 ( lt_of_le_of_lt hx εpos ); tauto );
  have h_dist : Tendsto (fun a => Metric.hausdorffDist ((C a).body : Set Plane) (C₀.body : Set Plane)) l (𝓝 0) := by
    convert ConvexSubbody.tendsto_hausdorffDist_zero hC using 1;
  filter_upwards [ h_dist.eventually ( gt_mem_nhds hd_pos ) ] with a ha;
  contrapose! ha;
  rw [ ← hd ];
  apply_rules [ Metric.infDist_le_hausdorffDist_of_mem ];
  apply_rules [ Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded ];
  · exact ⟨ x, ha ⟩;
  · exact C₀.nonempty;
  · exact ( C a ).isCompact.isBounded;
  · exact C₀.isCompact.isBounded

/-
**Interior stability.** A point in the interior of the limit body is eventually inside the
approximating bodies.
-/
theorem eventually_mem_of_mem_interior
    {α : Type*} {l : Filter α}
    {C : α → ConvexSubbody K} {C₀ : ConvexSubbody K}
    (hC : Tendsto C l (𝓝 C₀))
    {x : Plane} (hx : x ∈ interior (C₀.body : Set Plane)) :
    ∀ᶠ a in l, x ∈ ((C a).body : Set Plane) := by
  -- Since `x ∈ interior (C₀.body)` and `interior` is open, there is `ε > 0` with `Metric.ball x ε ⊆ interior (C₀.body) ⊆ (C₀.body)`.
  obtain ⟨ε, hε_pos, hε⟩ : ∃ ε > 0, Metric.closedBall x ε ⊆ (C₀.body : Set Plane) := by
    exact Metric.nhds_basis_closedBall.mem_iff.mp ( mem_interior_iff_mem_nhds.mp hx );
  -- From `ConvexSubbody.tendsto_hausdorffDist_zero hC`, eventually `Metric.hausdorffDist ((C a).body) (C₀.body) < ε`.
  have h_hausdorffDist : ∀ᶠ a in l, Metric.hausdorffDist ((C a).body : Set Plane) (C₀.body : Set Plane) < ε := by
    convert Filter.Tendsto.eventually ( ConvexSubbody.tendsto_hausdorffDist_zero hC ) ( gt_mem_nhds hε_pos ) using 1;
  filter_upwards [ h_hausdorffDist ] with a ha using mem_of_hausdorffDist_lt ( C a |> ConvexSubbody.convex ) ( C a |> ConvexSubbody.isCompact ) ( C a |> ConvexSubbody.nonempty ) ( C₀.isCompact.isBounded ) ( C₀.nonempty ) hε_pos ( by exact fun y hy => hε <| Metric.mem_closedBall.mpr <| by simpa using hy ) ha

/-
**Frontier-complement equivalence.** Off the frontier of the limit body, membership in the
approximating bodies eventually agrees with membership in the limit body.
-/
theorem eventually_mem_iff_of_not_mem_frontier
    {α : Type*} {l : Filter α}
    {C : α → ConvexSubbody K} {C₀ : ConvexSubbody K}
    (hC : Tendsto C l (𝓝 C₀))
    {x : Plane} (hx : x ∉ frontier (C₀.body : Set Plane)) :
    ∀ᶠ a in l,
      (x ∈ ((C a).body : Set Plane) ↔ x ∈ (C₀.body : Set Plane)) := by
  by_cases hx' : x ∈ (C₀.body : Set Plane);
  · have := NRR.ConvexSubbody.eventually_mem_of_mem_interior hC ( show x ∈ interior ( C₀.body : Set Plane ) from ?_ );
    · filter_upwards [ this ] with a ha using iff_of_true ha hx';
    · contrapose! hx;
      exact ⟨ subset_closure hx', hx ⟩;
  · filter_upwards [ NRR.ConvexSubbody.eventually_not_mem_of_not_mem hC hx' ] with a ha using iff_of_false ha hx'

end ConvexSubbody

end NRR
