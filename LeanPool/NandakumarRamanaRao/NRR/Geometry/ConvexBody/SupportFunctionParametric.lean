/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.SupportFunctionContinuity

/-!
# `NRR.Geometry.ConvexBody` — support-function continuity under body parameters

This module provides the *body-parameter* continuity API for the support function. the project
established continuity of `u ↦ h_K(u)` in the direction variable for a fixed body `K`; here we
package the joint continuity of

```text
(t, u) ↦ h_{K_t}(u)
```

when a family of convex bodies `K : α → ConvexBody E` varies continuously in the parameter `t`,
plus the closure properties (constant, translation, positive scaling) that later
partition-cell / perimeter continuity arguments need.

## Mathlib hyperspace / Hausdorff situation

Mathlib *does* have a metric-space structure on nonempty compact subsets:

* `Mathlib.Topology.MetricSpace.HausdorffDistance` defines `EMetric.hausdorffEdist` and
 `Metric.hausdorffDist` on arbitrary sets, with the standard estimates.
* `Mathlib.Topology.MetricSpace.Closeds` upgrades this to bona-fide
 `EMetricSpace (TopologicalSpace.NonemptyCompacts α)` (and `Compacts`, `Closeds`), and
 `Metric.NonemptyCompacts.dist_eq` states that the resulting metric `dist` coincides with
 `Metric.hausdorffDist`.

However this instance is an *`EMetricSpace`* on `NonemptyCompacts`, not a `ConvexBody`-level
topology, and wiring a `ConvexBody E → NonemptyCompacts E` map plus its induced topology in just to
obtain joint continuity would be a much larger hyperspace development than downstream modules
  require.
We therefore take the two-pronged approach the design allows:

* **Route A (quantitative Hausdorff bound).** We prove the sharp Lipschitz-type estimate
 `|h_K(u) − h_L(u)| ≤ d_H(K, L) · ‖u‖` (`abs_supportFunction_sub_le_hausdorffDist_mul_norm`),
 which is the bridge to any Hausdorff-metric continuity statement one might want later. It is
 stated with `Metric.hausdorffDist` on the underlying sets, the current mathlib name.

* **Route B (abstract family-continuity predicate).** We define
 `SupportFunctionContinuousFamily K` as joint continuity of `(t, u) ↦ h_{K_t}(u)` and prove the
 closure properties (`const`, `translate`, `scalePos`) together with the evaluation and
 unit-direction restriction lemmas. Later constructions can discharge
 `SupportFunctionContinuousFamily` directly for whatever concrete family they build.

## Public API

* `abs_supportFunction_sub_le_hausdorffDist_mul_norm`
* `SupportFunctionContinuousFamily`
* `supportFunction_continuous_family_eval`
* `SupportFunctionContinuousFamily.const`
* `SupportFunctionContinuousFamily.translate`
* `SupportFunctionContinuousFamily.scalePos`
* `supportFunction_continuous_family_on_unit_directions`
-/

@[expose] public section

namespace NRR.Geometry

namespace ConvexBody

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Route A — quantitative Hausdorff estimate -/

/-
**Hausdorff–Lipschitz estimate for the support function.** For two convex bodies the support
functions differ by at most `d_H(K, L) · ‖u‖`, where `d_H` is `Metric.hausdorffDist` on the
underlying sets. This is the bridge to Hausdorff-metric continuity of the support function.
-/
theorem abs_supportFunction_sub_le_hausdorffDist_mul_norm
    (K L : ConvexBody E) (u : E) :
    |supportFunction K u - supportFunction L u| ≤
      Metric.hausdorffDist (K : Set E) (L : Set E) * ‖u‖ := by
  refine abs_sub_le_iff.mpr ⟨ ?_, ?_ ⟩;
  · -- By definition of $d_H$, we know that for any $x \in K$, $d(x, L) \leq d_H(K, L)$.
    have h_dist_le : ∀ x ∈ K.carrier, Metric.infDist x L.carrier ≤ Metric.hausdorffDist
      K.carrier L.carrier := by
      intro x hx;
      apply Metric.infDist_le_hausdorffDist_of_mem hx;
      grind +suggestions;
    obtain ⟨ x, hx, hx' ⟩ := K.exists_supportPoint u;
    -- Since $L$ is compact and nonempty, there exists $y \in L$ such that $dist x y =
    -- Metric.infDist x L.carrier$.
    obtain ⟨ y, hy, hy' ⟩ : ∃ y ∈ L.carrier, dist x y = Metric.infDist x L.carrier := by
      have := L.isCompact.exists_infDist_eq_dist ( L.nonempty ) x; aesop;
    have h_inner_le : inner ℝ (x - y) u ≤ ‖x - y‖ * ‖u‖ := by
      exact real_inner_le_norm _ _;
    simp_all +decide only [mem_coe, dist_eq_norm, inner_sub_left, tsub_le_iff_right, ge_iff_le];
    exact h_inner_le.trans ( add_le_add ( mul_le_mul_of_nonneg_right ( h_dist_le x hx ) (
      norm_nonneg u ) ) ( L.inner_le_supportFunction hy ) );
  · obtain ⟨ x, hx, hx' ⟩ := L.exists_supportPoint u;
    -- Since $x \in L$, we have $\text{dist}(x, K) \leq \text{hausdorffDist}(L, K)$.
    have h_dist : Metric.infDist x K.carrier ≤ Metric.hausdorffDist L.carrier K.carrier := by
      apply Metric.infDist_le_hausdorffDist_of_mem hx;
      have h_bounded : Bornology.IsBounded (L.carrier : Set E) ∧ Bornology.IsBounded (K.carrier
        : Set E) := by
        exact ⟨ L.isCompact.isBounded, K.isCompact.isBounded ⟩;
      have h_nonempty : (L.carrier : Set E).Nonempty ∧ (K.carrier : Set E).Nonempty := by
        exact ⟨ ⟨ x, hx ⟩, K.nonempty ⟩;
      grind +suggestions;
    -- Since $K$ is compact and nonempty, there exists $y \in K$ such that $\text{dist}(x, y) =
    -- \text{infDist}(x, K)$.
    obtain ⟨ y, hy, hy' ⟩ : ∃ y ∈ K.carrier, dist x y = Metric.infDist x K.carrier := by
      have := K.isCompact.exists_infDist_eq_dist ( K.nonempty ) x; aesop;
    -- Using the triangle inequality and the definition of the support function, we have:
    have h_triangle : inner ℝ x u - inner ℝ y u ≤ ‖x - y‖ * ‖u‖ := by
      simpa [ inner_sub_left ] using abs_le.mp ( abs_real_inner_le_norm ( x - y ) u ) |>.2;
    simp_all +decide only
        [mem_coe, Metric.hausdorffDist_comm, dist_eq_norm, tsub_le_iff_right, ge_iff_le];
    exact h_triangle.trans ( add_le_add ( mul_le_mul_of_nonneg_right h_dist ( norm_nonneg u ) )
      ( ConvexBody.inner_le_supportFunction K hy ) )

/-! ### Route B — abstract family-continuity predicate -/

variable {α : Type*} [TopologicalSpace α]

/-- A family of convex bodies `K : α → ConvexBody E` is a *support-function continuous family* if
the map `(t, u) ↦ h_{K_t}(u)` is (jointly) continuous. This is the abstraction downstream
perimeter / partition-cell continuity arguments consume. -/
def SupportFunctionContinuousFamily (K : α → ConvexBody E) : Prop :=
  Continuous fun p : α × E => supportFunction (K p.1) p.2

/-- **Evaluation.** Unfolding the predicate: joint continuity of `(t, u) ↦ h_{K_t}(u)`. -/
theorem supportFunction_continuous_family_eval
    {K : α → ConvexBody E} (hK : SupportFunctionContinuousFamily K) :
    Continuous fun p : α × E => supportFunction (K p.1) p.2 :=
  hK

/-- **Constant family.** A constant family is a support-function continuous family, by the project's
`continuous_supportFunction`. -/
theorem SupportFunctionContinuousFamily.const (K : ConvexBody E) :
    SupportFunctionContinuousFamily (fun _ : α => K) :=
  K.continuous_supportFunction.comp continuous_snd

/-- **Translated family.** Translating a continuous family by a continuous vector field keeps it a
support-function continuous family, using `h_{K + a}(u) = ⟪a, u⟫ + h_K(u)`. -/
theorem SupportFunctionContinuousFamily.translate
    {K : α → ConvexBody E} (hK : SupportFunctionContinuousFamily K)
    (a : α → E) (ha : Continuous a) :
    SupportFunctionContinuousFamily (fun t => (K t).translate (a t)) := by
  unfold SupportFunctionContinuousFamily at hK ⊢
  simp only [supportFunction_translate]
  refine Continuous.add ?_ hK
  have : Continuous fun p : α × E => (inner ℝ (a p.1) p.2 : ℝ) := by
    fun_prop
  exact this

/-- **Positively scaled family.** Scaling a continuous family by a continuous positive function
keeps it a support-function continuous family, using `h_{r K}(u) = r · h_K(u)`. -/
theorem SupportFunctionContinuousFamily.scalePos
    {K : α → ConvexBody E} (hK : SupportFunctionContinuousFamily K)
    (r : α → ℝ) (hr : ∀ t, 0 < r t) (hcont : Continuous r) :
    SupportFunctionContinuousFamily (fun t => (K t).scalePos (r t) (hr t)) := by
  unfold SupportFunctionContinuousFamily at hK ⊢
  simp only [supportFunction_scalePos]
  exact (hcont.comp continuous_fst).mul hK

/-- **Restriction to unit directions.** The joint map restricted to the unit sphere
`Metric.sphere 0 1` is continuous. (the library has no bespoke sphere type; the ambient unit
sphere is used.) -/
theorem supportFunction_continuous_family_on_unit_directions
    {K : α → ConvexBody E} (hK : SupportFunctionContinuousFamily K) :
    Continuous fun p : α × (Metric.sphere (0 : E) 1) =>
      supportFunction (K p.1) (p.2 : E) :=
  hK.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

end ConvexBody

end NRR.Geometry
