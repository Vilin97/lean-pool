/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.LocallyConvex.Separation

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Epigraph separation for convex functions

This file records the project-local interface to Mathlib's geometric Hahn-Banach separation
theorem for strict epigraphs. It is intended for the endpoint-attainment step in the
Aleksandrov proof: supporting functionals are produced by applying Mathlib separation, not by
reproving Hahn-Banach.
-/

@[expose] public noncomputable section

open Set
open scoped Topology

namespace AleksandrovDifferentiability

variable {E : Type*} [NormedAddCommGroup E]

/-- The strict epigraph of a function over a set. -/
def strictEpigraphOn (s : Set E) (u : E → ℝ) : Set (E × ℝ) :=
  {p | p.1 ∈ s ∧ u p.1 < p.2}

/-- A convex function has a convex strict epigraph over its convexity domain. -/
theorem ConvexOn.convex_strictEpigraphOn {s : Set E} {u : E → ℝ}
    [NormedSpace ℝ E]
    (hu : ConvexOn ℝ s u) :
    Convex ℝ (strictEpigraphOn s u) := by
  simpa [strictEpigraphOn] using hu.convex_strict_epigraph

/-- If `u` is continuous on an open set, then its strict epigraph over that set is open. -/
theorem isOpen_strictEpigraphOn_of_continuousOn {s : Set E} {u : E → ℝ}
    (hs : IsOpen s) (hu : ContinuousOn u s) :
    IsOpen (strictEpigraphOn s u) := by
  rw [isOpen_iff_mem_nhds]
  rintro ⟨x, r⟩ ⟨hx, hlt⟩
  have hu_at : ContinuousAt u x :=
    hu.continuousAt (hs.mem_nhds hx)
  have hdiff :
      ContinuousAt (fun p : E × ℝ => u p.1 - p.2) (x, r) :=
    (hu_at.comp continuous_fst.continuousAt).sub continuous_snd.continuousAt
  have hlt_nhds :
      {p : E × ℝ | u p.1 - p.2 < 0} ∈ 𝓝 (x, r) :=
    hdiff (isOpen_Iio.mem_nhds (sub_neg.mpr hlt))
  have hbase_nhds : {p : E × ℝ | p.1 ∈ s} ∈ 𝓝 (x, r) :=
    continuous_fst.continuousAt (hs.mem_nhds hx)
  refine Filter.mem_of_superset (Filter.inter_mem hbase_nhds hlt_nhds) ?_
  intro p hp
  exact ⟨hp.1, sub_neg.mp hp.2⟩

/-- Apply Mathlib's geometric Hahn-Banach theorem to separate a point from the strict epigraph of
a convex function over an open set.

This is the project-local separation interface for later endpoint-attainment work. -/
theorem ConvexOn.exists_strongDual_lt_on_strictEpigraphOn
    {s : Set E} {u : E → ℝ} {x : E} {r : ℝ}
    [NormedSpace ℝ E]
    (hu : ConvexOn ℝ s u) (hs : IsOpen s) (hcont : ContinuousOn u s)
    (hx : (x, r) ∉ strictEpigraphOn s u) :
    ∃ ℓ : StrongDual ℝ (E × ℝ),
      ∀ p ∈ strictEpigraphOn s u, ℓ p < ℓ (x, r) :=
  geometric_hahn_banach_open_point
    (ConvexOn.convex_strictEpigraphOn hu)
    (isOpen_strictEpigraphOn_of_continuousOn hs hcont)
    hx

/-- On an open convex set in finite dimension, a convex function has open strict epigraph and
therefore admits the Mathlib separation conclusion for every point outside that strict epigraph. -/
theorem ConvexOn.exists_strongDual_lt_on_strictEpigraphOn_of_isOpen
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {s : Set E} {u : E → ℝ} {x : E} {r : ℝ}
    (hu : ConvexOn ℝ s u) (hs : IsOpen s)
    (hx : (x, r) ∉ strictEpigraphOn s u) :
    ∃ ℓ : StrongDual ℝ (E × ℝ),
      ∀ p ∈ strictEpigraphOn s u, ℓ p < ℓ (x, r) :=
  ConvexOn.exists_strongDual_lt_on_strictEpigraphOn hu hs (hu.continuousOn hs) hx

/-- A separator of the strict epigraph from the graph point `(x, u x)` has negative vertical
coefficient.

This is the first normalization fact needed to turn Mathlib's abstract separating functional into
an affine supporting functional for `u`. -/
theorem strictEpigraphOn_separatingFunctional_vertical_neg
    [NormedSpace ℝ E] {s : Set E} {u : E → ℝ} {x : E}
    (hx : x ∈ s) (ℓ : StrongDual ℝ (E × ℝ))
    (hsep : ∀ p ∈ strictEpigraphOn s u, ℓ p < ℓ (x, u x)) :
    ℓ (0, (1 : ℝ)) < 0 := by
  have hmem : (x, u x + 1) ∈ strictEpigraphOn s u := by
    simp [strictEpigraphOn, hx]
  have hlt := hsep (x, u x + 1) hmem
  have hdecomp : (x, u x + 1) = (x, u x) + (0, (1 : ℝ)) := by
    ext <;> simp
  rw [hdecomp, map_add] at hlt
  linarith

/-- Separation of the strict epigraph from a graph point, with the vertical negativity
normalization already extracted.

The separation itself is Mathlib's geometric Hahn-Banach theorem applied by
`ConvexOn.exists_strongDual_lt_on_strictEpigraphOn_of_isOpen`. -/
theorem ConvexOn.exists_strongDual_lt_on_strictEpigraphOn_graph_point_of_isOpen
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {s : Set E} {u : E → ℝ} {x : E}
    (hu : ConvexOn ℝ s u) (hs : IsOpen s) (hx : x ∈ s) :
    ∃ ℓ : StrongDual ℝ (E × ℝ),
      (∀ p ∈ strictEpigraphOn s u, ℓ p < ℓ (x, u x)) ∧ ℓ (0, (1 : ℝ)) < 0 := by
  have hnot : (x, u x) ∉ strictEpigraphOn s u := by
    simp [strictEpigraphOn]
  rcases ConvexOn.exists_strongDual_lt_on_strictEpigraphOn_of_isOpen hu hs hnot with ⟨ℓ, hsep⟩
  exact ⟨ℓ, hsep, strictEpigraphOn_separatingFunctional_vertical_neg hx ℓ hsep⟩

/-- The horizontal part of a separator, normalized by its negative vertical coefficient. -/
def strictEpigraphOn.normalizedHorizontalFunctional
    [NormedSpace ℝ E] (ℓ : StrongDual ℝ (E × ℝ)) : StrongDual ℝ E :=
  (-(ℓ (0, (1 : ℝ)))⁻¹) • (ℓ.comp (ContinuousLinearMap.inl ℝ E ℝ))

theorem strictEpigraphOn.normalizedHorizontalFunctional_apply
    [NormedSpace ℝ E] (ℓ : StrongDual ℝ (E × ℝ)) (v : E) :
    strictEpigraphOn.normalizedHorizontalFunctional ℓ v =
      -ℓ (v, (0 : ℝ)) / ℓ (0, (1 : ℝ)) := by
  simp [strictEpigraphOn.normalizedHorizontalFunctional, div_eq_mul_inv, mul_comm]

/-- The strict-epigraph separator also separates the closed graph pointwise. -/
theorem strictEpigraphOn_separatingFunctional_graph_le
    [NormedSpace ℝ E] {s : Set E} {u : E → ℝ} {x y : E}
    (hy : y ∈ s) (ℓ : StrongDual ℝ (E × ℝ))
    (hvert : ℓ (0, (1 : ℝ)) < 0)
    (hsep : ∀ p ∈ strictEpigraphOn s u, ℓ p < ℓ (x, u x)) :
    ℓ (y, u y) ≤ ℓ (x, u x) := by
  by_contra hnot
  have hbase_lt : ℓ (x, u x) < ℓ (y, u y) := lt_of_not_ge hnot
  let ε : ℝ := (ℓ (y, u y) - ℓ (x, u x)) / (2 * (-(ℓ (0, (1 : ℝ)))))
  have hden_pos : 0 < 2 * (-(ℓ (0, (1 : ℝ)))) := by
    exact mul_pos (by norm_num) (neg_pos.mpr hvert)
  have hε_pos : 0 < ε := by
    exact div_pos (sub_pos.mpr hbase_lt) hden_pos
  have hmem : (y, u y + ε) ∈ strictEpigraphOn s u := by
    exact ⟨hy, by linarith⟩
  have hlt := hsep (y, u y + ε) hmem
  have hdecomp : (y, u y + ε) = (y, u y) + ε • (0, (1 : ℝ)) := by
    ext <;> simp
  rw [hdecomp, map_add, map_smul] at hlt
  have hmul :
      ε * ℓ (0, (1 : ℝ)) = -(ℓ (y, u y) - ℓ (x, u x)) / 2 := by
    dsimp [ε]
    field_simp [ne_of_lt hvert]
  have hcontrary : ℓ (x, u x) < ℓ (y, u y) + ε * ℓ (0, (1 : ℝ)) := by
    rw [hmul]
    linarith
  exact hcontrary.not_ge hlt.le

/-- The normalized horizontal part of a strict-epigraph separator supports the function at the
separated graph point. -/
theorem strictEpigraphOn_normalizedHorizontalFunctional_supporting_inequality
    [NormedSpace ℝ E] {s : Set E} {u : E → ℝ} {x y : E}
    (hy : y ∈ s) (ℓ : StrongDual ℝ (E × ℝ))
    (hvert : ℓ (0, (1 : ℝ)) < 0)
    (hsep : ∀ p ∈ strictEpigraphOn s u, ℓ p < ℓ (x, u x)) :
    u x + strictEpigraphOn.normalizedHorizontalFunctional ℓ (y - x) ≤ u y := by
  have hgraph :=
    strictEpigraphOn_separatingFunctional_graph_le (s := s) (u := u) (x := x)
      hy ℓ hvert hsep
  have hgraph_expanded :
      ℓ (y, (0 : ℝ)) + u y * ℓ (0, (1 : ℝ)) ≤
        ℓ (x, (0 : ℝ)) + u x * ℓ (0, (1 : ℝ)) := by
    have hy_decomp : (y, u y) = (y, (0 : ℝ)) + u y • (0, (1 : ℝ)) := by
      ext <;> simp
    have hx_decomp : (x, u x) = (x, (0 : ℝ)) + u x • (0, (1 : ℝ)) := by
      ext <;> simp
    rw [hy_decomp, hx_decomp, map_add, map_smul, map_add, map_smul] at hgraph
    simpa [mul_comm] using hgraph
  have hsub :
      ℓ (y - x, (0 : ℝ)) = ℓ (y, (0 : ℝ)) - ℓ (x, (0 : ℝ)) := by
    have hdecomp : (y - x, (0 : ℝ)) = (y, (0 : ℝ)) - (x, (0 : ℝ)) := by
      ext <;> simp
    rw [hdecomp, map_sub]
  set a : ℝ := ℓ (0, (1 : ℝ))
  set byv : ℝ := ℓ (y, (0 : ℝ))
  set bxv : ℝ := ℓ (x, (0 : ℝ))
  have ha : a < 0 := by simpa [a] using hvert
  have hgraph_ab : byv + u y * a ≤ bxv + u x * a := by
    simpa [a, byv, bxv] using hgraph_expanded
  rw [strictEpigraphOn.normalizedHorizontalFunctional_apply, hsub]
  change u x + -(byv - bxv) / a ≤ u y
  have hpos : 0 < -a := neg_pos.mpr ha
  have hmul : (-a) * (u x + -(byv - bxv) / a) ≤ (-a) * u y := by
    have hleft :
        (-a) * (u x + -(byv - bxv) / a) = -a * u x + (byv - bxv) := by
      field_simp [ne_of_lt ha]
      ring
    rw [hleft]
    nlinarith [hgraph_ab]
  exact (mul_le_mul_iff_right₀ hpos).mp hmul

/-- A convex function on an open finite-dimensional domain admits a supporting continuous
linear functional at every point of the domain.

This is the graph-point consequence of Mathlib epigraph separation. Endpoint-specific arguments
will add the extra normalization `q = ℓ z`; this theorem supplies the ambient support inequality
itself. -/
theorem ConvexOn.exists_supportingFunctionalAt_of_isOpen
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {s : Set E} {u : E → ℝ} {x : E}
    (hu : ConvexOn ℝ s u) (hs : IsOpen s) (hx : x ∈ s) :
    ∃ φ : StrongDual ℝ E, ∀ y ∈ s, u x + φ (y - x) ≤ u y := by
  rcases ConvexOn.exists_strongDual_lt_on_strictEpigraphOn_graph_point_of_isOpen
      hu hs hx with
    ⟨ℓ, hsep, hvert⟩
  exact
    ⟨strictEpigraphOn.normalizedHorizontalFunctional ℓ,
      fun y hy =>
        strictEpigraphOn_normalizedHorizontalFunctional_supporting_inequality
          hy ℓ hvert hsep⟩

end AleksandrovDifferentiability
