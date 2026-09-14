/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import LeanPool.Schoenflies.RealizeSubdiv
import LeanPool.Schoenflies.ArcMonotone

/-!
# Transporting a skeleton homeomorphism across an edge subdivision

`Schoenflies/RealizeSubdiv.lean` builds `SubdivData.realize`, the realization of a subdivided
cell structure, and closes with the observation that it does **not** move the realized
1-skeleton (`SubdivData.skeletonSet_realize`). It also names what was missing: a
`CellStructure.SkeletonHomeo` between two realizations does not, by itself, carry the *half*
arcs of a subdivided edge onto each other. That gap is what `Schoenflies/ArcMonotone.lean`
fills, and this module spends.

`SubdivData.realizeHomeo` is the transported homeomorphism. As a point map it is *unchanged* —
`realizeHomeo_toFun` is `rfl` — which is exactly what `CellStructure.LimitTower.skelHomeo_succ`
in `Schoenflies/LimitMap.lean` asks for ("an edge subdivision leaves the skeleton map unchanged
as a point map"), and through it `Schoenflies.StageSequence`.

## The target parameter, and the two orientations

Subdividing at parameter `t` on the source side means subdividing at the parameter on the
target side where `R₂.drawing d.edge` sits at `g.toFun (R₁.drawing d.edge t)`. That is
`SubdivData.targetParam`, a plain `def` built from `Schoenflies.transferParam`; a caller never
has to guess it, and `SubdivData.drawing_targetParam` is its defining property.

`RealizeSubdiv.lean` warns that `IsDrawing.edge_param` is orientation-free, so `drawing e 0` may
be either end of `e`, and reads the orientation off with `SubdivData.leftParam`. The same issue
arises here on the `R₂` side, **and it is not forced**: the two realizations are independent
data, so nothing prevents `R₁` from drawing `d.edge` from `d.left` and `R₂` from drawing it from
`d.right`. This module does not assume otherwise. It does not need a second case distinction
either, because the transfer map handles it:

  `SubdivData.targetParam_leftParam` : `targetParam (leftParam R₁) = leftParam R₂`

holds whatever the two orientations are — `g` carries `R₁.pos d.left` to `R₂.pos d.left`, and
`leftParam R₂` is by definition the parameter sitting there. Correspondingly the arc identity
imported from `ArcMonotone` is stated over `uIcc`, which is unordered, so the two halves match
up without either orientation ever being named. The one place the orientations do surface is
`SubdivData.targetParam_ends`, which records that the pair `(targetParam 0, targetParam 1)` is
`(0, 1)` or `(1, 0)` — the input `ArcMonotone.param_mem_Ioo_of_ends` needs to know the new
target parameter is interior.

## Blueprint

* `def:matched-pair`, clause 3 — the transported `edgeArc_image` at the two new 1-cells is
  precisely "on each corresponding pair of edges, `g` restricts to a chosen homeomorphism
  between them, matching endpoints", propagated through operation 1.
* `def:generated-structure`, operation 1 (edge subdivision) — "the corresponding point is
  inserted into the corresponding edge"; `SubdivData.targetParam` is "corresponding".

Declarations:

* `Schoenflies.CellStructure.SubdivData.arcMatch_edge` — the drawn subdivided edge, its image,
  and `g` between them, as an `ArcMatch`.
* `Schoenflies.CellStructure.SubdivData.targetParam` — the corresponding parameter on the target
  side, with `drawing_targetParam`, `targetParam_leftParam`, `targetParam_rightParam`,
  `targetParam_ends`, `targetParam_mem_Ioo`.
* `Schoenflies.CellStructure.SubdivData.realizeHomeo` — the transported skeleton homeomorphism,
  with `realizeHomeo_toFun` / `realizeHomeo_invFun` / `realizeHomeo_eqOn`.
-/

open Set unitInterval
open scoped Graph

namespace Schoenflies

open Graph

namespace CellStructure

namespace SubdivData

variable {γ : Type*} {S : CellStructure γ} {R₁ R₂ : S.Realization}
  (d : S.SubdivData) (g : SkeletonHomeo R₁ R₂) {t : ℝ}

/-! ### The drawn subdivided edge, on both sides -/

theorem edgeArc_subset_skeletonSet (R : S.Realization) :
    R.drawing d.edge '' I ⊆ R.skeletonSet :=
  edgeArc_subset_pointSet (d.edge_mem_edgeSet_graph R)

/-- **The subdivided edge is drawn on both sides, and `g` carries one drawing onto the other.**
Everything the arc-monotonicity machinery needs, assembled from fields of `R₁`, `R₂` and `g`;
no new hypothesis. -/
theorem arcMatch_edge : ArcMatch (R₁.drawing d.edge) (R₂.drawing d.edge) g.toFun where
  continuousOn_src := d.continuousOn_drawing_edge R₁
  injOn_src := d.injOn_drawing_edge R₁
  continuousOn_tgt := d.continuousOn_drawing_edge R₂
  injOn_tgt := d.injOn_drawing_edge R₂
  continuousOn_map := g.continuousOn_toFun.mono (d.edgeArc_subset_skeletonSet R₁)
  injOn_map := g.injOn.mono (d.edgeArc_subset_skeletonSet R₁)
  image_eq := g.edgeArc_image d.edge_mem_edgeSet

/-! ### The corresponding parameter on the target side -/

/-- **The parameter at which the target drawing sits at the image of the source point.**

A `def`, not an existential: the subdivided target realization is `d.realize R₂ (d.targetParam g
t) _`, and every lemma below refers to it by name. -/
noncomputable def targetParam (d : S.SubdivData) (g : SkeletonHomeo R₁ R₂) (t : ℝ) : ℝ :=
  transferParam (R₁.drawing d.edge) (R₂.drawing d.edge) g.toFun t

theorem targetParam_mem_I (ht : t ∈ I) : d.targetParam g t ∈ I :=
  (d.arcMatch_edge g).param_mem_I ht

/-- **The defining property of the target parameter.** -/
theorem drawing_targetParam (ht : t ∈ I) :
    R₂.drawing d.edge (d.targetParam g t) = g.toFun (R₁.drawing d.edge t) :=
  (d.arcMatch_edge g).apply_param ht

/-- The endpoint of the subdivided edge at `d.left` corresponds to the endpoint at `d.left`,
whichever way round either realization happens to draw the edge. -/
theorem targetParam_leftParam : d.targetParam g (d.leftParam R₁) = d.leftParam R₂ := by
  refine (d.arcMatch_edge g).param_eq (d.leftParam_mem_I R₂) ?_
  rw [d.drawing_leftParam R₂, d.drawing_leftParam R₁]
  exact (g.pos_apply d.isLink.left_mem).symm

/-- …and likewise at `d.right`. -/
theorem targetParam_rightParam : d.targetParam g (d.rightParam R₁) = d.rightParam R₂ := by
  refine (d.arcMatch_edge g).param_eq (d.rightParam_mem_I R₂) ?_
  rw [d.drawing_rightParam R₂, d.drawing_rightParam R₁]
  exact (g.pos_apply d.isLink.right_mem).symm

/-- **The two endpoint parameters go to the two endpoint parameters**, in one order or the
other. This is the only statement in the file that mentions the orientations at all, and it is
here only because interiority of the new target parameter needs it. -/
theorem targetParam_ends :
    (d.targetParam g 0 = 0 ∧ d.targetParam g 1 = 1) ∨
      (d.targetParam g 0 = 1 ∧ d.targetParam g 1 = 0) := by
  have hL := d.targetParam_leftParam g
  have hR := d.targetParam_rightParam g
  rw [rightParam, rightParam] at hR
  rcases d.leftParam_eq_zero_or_one R₁ with h1 | h1 <;>
      rcases d.leftParam_eq_zero_or_one R₂ with h2 | h2 <;>
      simp only [h1, h2, sub_zero, sub_self] at hL hR
  · exact Or.inl ⟨hL, hR⟩
  · exact Or.inr ⟨hL, hR⟩
  · exact Or.inr ⟨hR, hL⟩
  · exact Or.inl ⟨hR, hL⟩

/-- **An interior source parameter has an interior target parameter** — so the target
realization can be subdivided at it. -/
theorem targetParam_mem_Ioo (ht : t ∈ Ioo (0 : ℝ) 1) : d.targetParam g t ∈ Ioo (0 : ℝ) 1 :=
  (d.arcMatch_edge g).param_mem_Ioo_of_ends (d.targetParam_ends g) ht

/-- **`g` carries a piece of the drawn edge onto the corresponding piece.** The whole content of
`Schoenflies/ArcMonotone.lean`, specialized to the subdivided edge. -/
theorem image_edge_uIcc {s u : ℝ} (hs : s ∈ I) (hu : u ∈ I) :
    g.toFun '' (R₁.drawing d.edge '' uIcc s u) =
      R₂.drawing d.edge '' uIcc (d.targetParam g s) (d.targetParam g u) :=
  (d.arcMatch_edge g).image_image_uIcc hs hu

/-! ### The transported skeleton homeomorphism -/

/-- **The skeleton homeomorphism, transported across an edge subdivision.**

The point map is untouched: a subdivision does not move the realized 1-skeleton
(`skeletonSet_realize`), so six of the eight fields are the old ones read through that equality.
The two that are not — `pos_apply` at the new 0-cell and `edgeArc_image` at the two new 1-cells
— are `drawing_targetParam` and `image_edge_uIcc`. -/
noncomputable def realizeHomeo (d : S.SubdivData) (g : SkeletonHomeo R₁ R₂) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    SkeletonHomeo (d.realize R₁ t ht)
      (d.realize R₂ (d.targetParam g t) (d.targetParam_mem_Ioo g ht)) where
  toFun := g.toFun
  invFun := g.invFun
  continuousOn_toFun := by
    rw [skeletonSet_realize ht]; exact g.continuousOn_toFun
  continuousOn_invFun := by
    rw [skeletonSet_realize (d.targetParam_mem_Ioo g ht)]; exact g.continuousOn_invFun
  leftInvOn := by
    rw [skeletonSet_realize ht]; exact g.leftInvOn
  rightInvOn := by
    rw [skeletonSet_realize (d.targetParam_mem_Ioo g ht)]; exact g.rightInvOn
  pos_apply := by
    intro v hv
    rw [subdivideEdge_skel, d.skeleton_vertexSet, mem_insert_iff] at hv
    simp only [realize_pos]
    rcases hv with rfl | hv
    · rw [realizePos_newVertex, realizePos_newVertex]
      exact (d.drawing_targetParam g (Ioo_subset_Icc_self ht)).symm
    · rw [realizePos_of_mem_vertexSet hv, realizePos_of_mem_vertexSet hv]
      exact g.pos_apply hv
  edgeArc_image := by
    intro e he
    rw [subdivideEdge_skel, d.skeleton_edgeSet] at he
    simp only [mem_insert_iff, mem_sdiff, mem_singleton_iff] at he
    simp only [realize_drawing]
    rcases he with rfl | rfl | ⟨heS, hee⟩
    · -- The first new edge: the half from `d.left` to the new point, on both sides.
      rw [edgeArc_newEdge₁, edgeArc_newEdge₁,
        d.image_edge_uIcc g (d.leftParam_mem_I R₁) (Ioo_subset_Icc_self ht),
        d.targetParam_leftParam g]
    · -- The second new edge: the half from the new point to `d.right`.
      rw [edgeArc_newEdge₂, edgeArc_newEdge₂,
        d.image_edge_uIcc g (Ioo_subset_Icc_self ht) (d.rightParam_mem_I R₁),
        d.targetParam_rightParam g]
    · -- An untouched edge: both drawings are the old ones.
      have hc := S.mem_cells_of_mem_edgeSet heS
      rw [edgeArc_of_ne (d.ne_newEdge₁_of_mem_cells hc) (d.ne_newEdge₂_of_mem_cells hc),
        edgeArc_of_ne (d.ne_newEdge₁_of_mem_cells hc) (d.ne_newEdge₂_of_mem_cells hc)]
      exact g.edgeArc_image heS

@[simp] theorem realizeHomeo_toFun (ht : t ∈ Ioo (0 : ℝ) 1) :
    (d.realizeHomeo g ht).toFun = g.toFun := rfl

@[simp] theorem realizeHomeo_invFun (ht : t ∈ Ioo (0 : ℝ) 1) :
    (d.realizeHomeo g ht).invFun = g.invFun := rfl

/-- **The transported map is the old one as a point map** — the form
`CellStructure.LimitTower.skelHomeo_succ` consumes. -/
theorem realizeHomeo_eqOn (ht : t ∈ Ioo (0 : ℝ) 1) {A : Set Plane} :
    EqOn (d.realizeHomeo g ht).toFun g.toFun A := fun _ _ => rfl

end SubdivData

end CellStructure

end Schoenflies
