/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody.HalfspaceCoefficients
public import LeanPool.NandakumarRamanaRao.NRR.HalfSpace

/-!
# `NRR.EMP.VariableBody.IndicatorStability` — a.e. stability of cell indicators

For a variable planar body `C : BodySpace K A`, a configuration `s : Config n`, and weights
`w : Fin n → ℝ`, the restricted power cell of site `i` is the parent body intersected with finitely
many closed lower halfspaces. When the body, sites, and weights tend to a limit along an arbitrary
filter, the `0/1` indicator of the restricted cell converges pointwise almost everywhere to the
indicator of the limiting cell.

The exceptional null set is explicit:

```text
frontier(C₀)
∪ ⋃ j : {j // j ≠ i},
    {x | ⟪sepNormal s₀ i j, x⟫ = sepOffset s₀ w₀ i j}
```

The parent frontier is Lebesgue-null (`ConvexSubbody.frontier_null`), and every off-diagonal wall is
Lebesgue-null because the separating normal is nonzero (`sepNormal_ne_zero`,
`NRR.Halfspace.hyperplane_null`). Outside this set the point avoids the limiting parent
frontier, so `BodySpace.eventually_mem_iff_of_not_mem_frontier` controls the parent membership, and
each off-diagonal scalar `⟪sepNormal (s a) i j, x⟫ - sepOffset (s a) (w a) i j` tends to a nonzero
limit, hence has eventually constant sign. Combining finitely many eventual statements and rewriting
membership through `cellSet_eq_offDiag_halfspaces` gives eventual membership equivalence, which
converts to convergence of the indicator.

This module uses no compactness of `Config n` and no continuity of the normalized weight; it is an
input to area continuity, not the reverse.
-/

@[expose] public section

open MeasureTheory Filter Topology
open NRR NRR.Geometry NRR.Geometry.ConvexBody
open scoped RealInnerProductSpace
namespace NRR.EMP.VariableBody

variable {K : Geometry.ConvexBody Plane} {A : ℝ} {n : ℕ} (hA : 0 < A)

/-- **Eventual membership equivalence at a good point.** If `x` avoids the frontier of the limiting
parent body and all limiting off-diagonal walls, then eventually along the filter, membership of `x`
in the moving cell agrees with membership in the limiting cell. -/
theorem eventually_cell_membership_eq_of_goodPoint
    {α : Type*} {l : Filter α}
    {C : α → BodySpace K A} {C₀ : BodySpace K A}
    {s : α → Config n} {s₀ : Config n}
    {w : α → Fin n → ℝ} {w₀ : Fin n → ℝ}
    (hC : Tendsto C l (𝓝 C₀))
    (hs : Tendsto s l (𝓝 s₀))
    (hw : Tendsto w l (𝓝 w₀))
    (i : Fin n) (x : Plane)
    (hxParent : x ∉ frontier (C₀.body : Set Plane))
    (hxWalls :
      ∀ j : {j : Fin n // j ≠ i},
        ⟪sepNormal s₀ i j.1, x⟫ ≠ sepOffset s₀ w₀ i j.1) :
    ∀ᶠ a in l,
      (x ∈ cellSet hA (C a) (s a) (w a) i ↔
       x ∈ cellSet hA C₀ s₀ w₀ i) := by
  -- Parent membership is eventually stable off the limiting frontier.
  have hP :
      ∀ᶠ a in l,
        (x ∈ ((C a).body : Set Plane) ↔ x ∈ (C₀.body : Set Plane)) :=
    NRR.BodySpace.eventually_mem_iff_of_not_mem_frontier hC hxParent
  -- Each off-diagonal halfspace membership is eventually stable at a good point.
  have hW :
      ∀ᶠ a in l, ∀ j : {j : Fin n // j ≠ i},
        (⟪sepNormal (s a) i j.1, x⟫ ≤ sepOffset (s a) (w a) i j.1 ↔
         ⟪sepNormal s₀ i j.1, x⟫ ≤ sepOffset s₀ w₀ i j.1) := by
    rw [Filter.eventually_all]
    intro j
    -- Component convergences, avoiding the product topology on `Config n × (Fin n → ℝ)`.
    have hpts : Tendsto (fun a => (s a).pts) l (𝓝 s₀.pts) :=
      (Config.continuous_pts.tendsto s₀).comp hs
    have hptsj : Tendsto (fun a => (s a).pts j.1) l (𝓝 (s₀.pts j.1)) :=
      ((continuous_apply j.1).tendsto s₀.pts).comp hpts
    have hptsi : Tendsto (fun a => (s a).pts i) l (𝓝 (s₀.pts i)) :=
      ((continuous_apply i).tendsto s₀.pts).comp hpts
    have hwj : Tendsto (fun a => (w a) j.1) l (𝓝 (w₀ j.1)) :=
      ((continuous_apply j.1).tendsto w₀).comp hw
    have hwi : Tendsto (fun a => (w a) i) l (𝓝 (w₀ i)) :=
      ((continuous_apply i).tendsto w₀).comp hw
    have hInner :
        Tendsto (fun a => ⟪sepNormal (s a) i j.1, x⟫) l
          (𝓝 (⟪sepNormal s₀ i j.1, x⟫)) := by
      simp only [sepNormal, PowerDiagram.sepNormal]
      exact ((hptsj.sub hptsi).const_smul (2 : ℝ)).inner tendsto_const_nhds
    have hOffset :
        Tendsto (fun a => sepOffset (s a) (w a) i j.1) l
          (𝓝 (sepOffset s₀ w₀ i j.1)) := by
      simp only [sepOffset, PowerDiagram.sepOffset]
      exact (((hptsj.norm.pow 2).sub (hptsi.norm.pow 2)).sub hwj).add hwi
    have hD :
        Tendsto
          (fun a => ⟪sepNormal (s a) i j.1, x⟫ - sepOffset (s a) (w a) i j.1) l
          (𝓝 (⟪sepNormal s₀ i j.1, x⟫ - sepOffset s₀ w₀ i j.1)) :=
      hInner.sub hOffset
    have hne : ⟪sepNormal s₀ i j.1, x⟫ - sepOffset s₀ w₀ i j.1 ≠ 0 :=
      sub_ne_zero.mpr (hxWalls j)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · filter_upwards [hD.eventually (Iio_mem_nhds hlt)] with a ha
      exact iff_of_true (by linarith) (by linarith)
    · filter_upwards [hD.eventually (Ioi_mem_nhds hgt)] with a ha
      exact iff_of_false (not_le.mpr (by linarith)) (not_le.mpr (by linarith))
  filter_upwards [hP, hW] with a hPa hWa
  rw [cellSet_eq_offDiag_halfspaces, cellSet_eq_offDiag_halfspaces]
  simp only [Set.mem_inter_iff, Set.mem_iInter, Geometry.mem_lowerClosedHalfspace]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨hPa.mp h1, fun j => (hWa j).mp (h2 j)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨hPa.mpr h1, fun j => (hWa j).mpr (h2 j)⟩

/-- **Almost-everywhere stability of the cell indicator.** As the body, sites, and weights tend to a
limit along an arbitrary filter, the `0/1` indicator of the restricted power cell of site `i`
converges pointwise almost everywhere to the indicator of the limiting cell. -/
theorem tendsto_cell_indicator_ae
    {α : Type*} {l : Filter α}
    {C : α → BodySpace K A} {C₀ : BodySpace K A}
    {s : α → Config n} {s₀ : Config n}
    {w : α → Fin n → ℝ} {w₀ : Fin n → ℝ}
    (hC : Tendsto C l (𝓝 C₀))
    (hs : Tendsto s l (𝓝 s₀))
    (hw : Tendsto w l (𝓝 w₀))
    (i : Fin n) :
    ∀ᵐ x ∂volume,
      Tendsto
        (fun a =>
          (cellSet hA (C a) (s a) (w a) i).indicator
            (fun _ => (1 : ℝ)) x)
        l
        (𝓝
          ((cellSet hA C₀ s₀ w₀ i).indicator
            (fun _ => (1 : ℝ)) x)) := by
  -- The explicit exceptional set: the limiting parent frontier together with all limiting walls.
  set N : Set Plane :=
      frontier (C₀.body : Set Plane) ∪
        ⋃ j : {j : Fin n // j ≠ i},
          {x : Plane | ⟪sepNormal s₀ i j.1, x⟫ = sepOffset s₀ w₀ i j.1} with hNdef
  have hFrontNull : volume (frontier (C₀.body : Set Plane)) = 0 :=
    ConvexSubbody.frontier_null C₀.body
  have hWallNull :
      volume
        (⋃ j : {j : Fin n // j ≠ i},
          {x : Plane | ⟪sepNormal s₀ i j.1, x⟫ = sepOffset s₀ w₀ i j.1}) = 0 := by
    apply measure_iUnion_null_iff.mpr
    intro j
    exact NRR.Halfspace.hyperplane_null (sepNormal_ne_zero s₀ (Ne.symm j.2)) _
  have hNnull : volume N = 0 := by
    rw [hNdef]
    exact measure_union_null hFrontNull hWallNull
  have hNae : ∀ᵐ x ∂volume, x ∉ N := by
    rw [ae_iff]
    simpa using hNnull
  filter_upwards [hNae] with x hx
  -- Extract the good-point conditions from `x ∉ N`.
  have hxParent : x ∉ frontier (C₀.body : Set Plane) := fun h => hx (Or.inl h)
  have hxWalls :
      ∀ j : {j : Fin n // j ≠ i},
        ⟪sepNormal s₀ i j.1, x⟫ ≠ sepOffset s₀ w₀ i j.1 := by
    intro j heq
    exact hx (Or.inr (Set.mem_iUnion.mpr ⟨j, heq⟩))
  -- Eventual membership equivalence yields eventual indicator equality.
  have hmem :=
    eventually_cell_membership_eq_of_goodPoint hA hC hs hw i x hxParent hxWalls
  have heqind :
      (fun _ : α => (cellSet hA C₀ s₀ w₀ i).indicator (fun _ => (1 : ℝ)) x)
        =ᶠ[l]
      (fun a => (cellSet hA (C a) (s a) (w a) i).indicator (fun _ => (1 : ℝ)) x) := by
    filter_upwards [hmem] with a ha
    by_cases hxa : x ∈ cellSet hA (C a) (s a) (w a) i
    · rw [Set.indicator_of_mem (ha.mp hxa), Set.indicator_of_mem hxa]
    · rw [Set.indicator_of_notMem (fun h => hxa (ha.mpr h)),
        Set.indicator_of_notMem hxa]
  exact tendsto_const_nhds.congr' heqind

end NRR.EMP.VariableBody
