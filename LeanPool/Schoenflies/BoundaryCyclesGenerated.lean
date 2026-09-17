/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import LeanPool.Schoenflies.BoundaryCycles
import LeanPool.Schoenflies.CellulationInvariants

/-!
# Boundary cycles under the elementary cellulation operations

This module proves that the face-boundary invariant used to construct the two paths of an ear
step is closed under face splitting and edge subdivision.  The split proof is combinatorial:
each new boundary is one old boundary arc followed by the reverse of the inserted ear.

## Blueprint

* `Schoenflies.CellStructure.SplitData.boundaryCycles` — preservation under operation 2 of
  `def:generated-structure`.
* `Schoenflies.CellStructure.SubdivData.boundaryCycles` — preservation under operation 1.
* `Schoenflies.GeneratedStructure.boundaryCycles` — the closed induction.
-/

open Set
open scoped Graph

namespace Schoenflies

namespace CellStructure

variable {γ : Type*} {S : CellStructure γ}

namespace SplitData

variable (d : S.SplitData)

/-- An old walk visits the same vertices when read in the enlarged skeleton. -/
theorem walkVertices_oldWalk {u v : γ} {W : List γ} (h : S.skel.IsWalk u W v) :
    d.skeleton.walkVertices u W = S.skel.walkVertices u W := by
  apply Set.Subset.antisymm
  · intro z hz
    rcases Graph.mem_walkVertices_iff.1 hz with rfl | ⟨f, hf, y, hlink⟩
    · exact Graph.mem_walkVertices_self
    · rw [SplitData.skeleton, d.compatible.union_isLink] at hlink
      rcases hlink with hlink | hlink
      · exact Graph.mem_walkVertices_of_mem_covered ⟨f, hf, y, hlink⟩
      · exact (Set.disjoint_left.1 d.disjoint_edgeSet (h.edge_mem hf)
          hlink.edge_mem).elim
  · exact Graph.walkVertices_mono_of_le d.le_skeleton

/-- The ear walk visits exactly the vertices of the abstract ear graph, even when read in the
enlarged skeleton. -/
theorem walkVertices_earWalk :
    d.skeleton.walkVertices d.source d.earWalk = V(d.ear) := by
  apply Set.Subset.antisymm
  · intro z hz
    rcases Graph.mem_walkVertices_iff.1 hz with rfl | ⟨f, hf, y, hlink⟩
    · exact d.isPathGraph.source_mem
    · rw [SplitData.skeleton, d.compatible.union_isLink] at hlink
      rcases hlink with hlink | hlink
      · exact (Set.disjoint_left.1 d.disjoint_edgeSet hlink.edge_mem
          (d.isPathGraph.mem_edgeSet hf)).elim
      · exact hlink.left_mem
  · rw [d.isPathGraph.vertexSet_eq]
    exact Graph.walkVertices_mono_of_le d.ear_le_skeleton

/-- The reverse ear walk has the same vertex carrier. -/
theorem walkVertices_reverse_earWalk :
    d.skeleton.walkVertices d.target d.earWalk.reverse = V(d.ear) := by
  rw [(d.isPathGraph.isWalk.mono d.ear_le_skeleton).reverse_walkVertices]
  exact d.walkVertices_earWalk

/-- The cells of an old walk are unchanged in the enlarged skeleton. -/
theorem pathCells_oldWalk {u v : γ} {W : List γ} (h : S.skel.IsWalk u W v) :
    (S.splitFace d).pathCells u W = S.pathCells u W := by
  rw [CellStructure.pathCells, CellStructure.pathCells, splitFace_skel,
    d.walkVertices_oldWalk h]

/-- The cells of the ear walk, read in the enlarged skeleton, are exactly the cells of the
abstract ear graph. -/
theorem pathCells_earWalk :
    (S.splitFace d).pathCells d.source d.earWalk = d.earCells := by
  rw [CellStructure.pathCells, splitFace_skel, d.walkVertices_earWalk, SplitData.earCells,
    d.isPathGraph.edgeSet_eq]
  exact Set.union_comm _ _

/-- Reversing the ear walk does not change its cell carrier. -/
theorem pathCells_reverse_earWalk :
    (S.splitFace d).pathCells d.target d.earWalk.reverse = d.earCells := by
  rw [FaceCycle.pathCells_reverse (d.isPathGraph.isPath.mono d.ear_le_skeleton).isWalk]
  exact d.pathCells_earWalk

/-- One old boundary path closed by the reverse ear is a boundary cycle of a new face. -/
theorem faceCycle_of_boundaryPath {newFace : γ} {P : List γ}
    (hface : newFace ∈ (S.splitFace d).faces)
    (hboundary : (S.splitFace d).boundary newFace = P ++ d.earWalk.reverse)
    (hP : S.skel.IsPath d.source P d.target)
    (hsub : ∀ ⦃σ : γ⦄, (S.splitFace d).sub σ newFace ↔
      σ = newFace ∨ σ ∈ d.earCells ∨ σ ∈ S.pathCells d.source P) :
    Nonempty ((S.splitFace d).FaceCycle newFace) := by
  have hPne : P ≠ [] := hP.ne_nil d.source_ne_target
  cases P with
  | nil => exact (hPne rfl).elim
  | cons f R => cases hP with
  | @cons _ w _ _ _ hlink hR hfresh =>
    have hR' := hR.mono d.le_skeleton
    have hQ' := d.isPathGraph.isPath.reverse.mono d.ear_le_skeleton
    have hmeet : ∀ y ∈ d.skeleton.walkVertices w R,
        y ∈ d.skeleton.walkVertices d.target d.earWalk.reverse → y = d.target := by
      intro y hyR hyQ
      have hyOld : y ∈ S.skel.walkVertices w R := by
        rw [← d.walkVertices_oldWalk hR.isWalk]
        exact hyR
      have hyEar : y ∈ V(d.ear) := d.walkVertices_reverse_earWalk ▸ hyQ
      have hyEnds : y ∈ ({d.source, d.target} : Set γ) := by
        rw [← d.vertexSet_inter]
        exact ⟨hyEar, hR.isWalk.walkVertices_subset hyOld⟩
      rcases hyEnds with rfl | rfl
      · exact (hfresh hyOld).elim
      · rfl
    have hpath : d.skeleton.IsPath w (R ++ d.earWalk.reverse) d.source :=
      hR'.append hQ' hmeet
    have hfreshEdge : f ∉ R ++ d.earWalk.reverse := by
      rw [List.mem_append, List.mem_reverse]
      rintro (hfR | hfQ)
      · exact (List.nodup_cons.1 (Graph.IsPath.nodup (.cons hlink hR hfresh))).1 hfR
      · exact Set.disjoint_left.1 d.disjoint_edgeSet hlink.edge_mem
          (d.isPathGraph.mem_edgeSet hfQ)
    have hcarrier : (S.splitFace d).pathCells d.source
          ((f :: R) ++ d.earWalk.reverse) =
        S.pathCells d.source (f :: R) ∪ d.earCells := by
      calc
        (S.splitFace d).pathCells d.source ((f :: R) ++ d.earWalk.reverse) =
            (S.splitFace d).pathCells d.source (f :: R) ∪
              (S.splitFace d).pathCells d.target d.earWalk.reverse :=
          FaceCycle.pathCells_append
            ((Graph.IsWalk.cons hlink hR.isWalk).mono d.le_skeleton)
            hQ'.isWalk
        _ = S.pathCells d.source (f :: R) ∪ d.earCells := by
          rw [d.pathCells_oldWalk (Graph.IsWalk.cons hlink hR.isWalk),
            d.pathCells_reverse_earWalk]
    refine ⟨{
      face_mem := hface
      edge := f
      source := w
      target := d.source
      walk := R ++ d.earWalk.reverse
      boundary_eq := hboundary
      isCycle := ⟨hlink.symm.mono d.le_skeleton, hpath, hfreshEdge⟩
      sub_face := ?_
    }⟩
    intro σ
    rw [hsub]
    change (σ = newFace ∨ σ ∈ d.earCells ∨ σ ∈ S.pathCells d.source (f :: R)) ↔
      σ = newFace ∨ σ ∈ (S.splitFace d).pathCells d.source
        ((f :: R) ++ d.earWalk.reverse)
    rw [hcarrier]
    simp only [Set.mem_union]
    tauto

/-- Face splitting preserves cyclic boundaries. -/
theorem boundaryCycles (hcycles : S.BoundaryCycles) (hS : S.CombInvariants) :
    (S.splitFace d).BoundaryCycles where
  cycle F hF := by
    rw [splitFace_faces] at hF
    rcases hF with rfl | rfl | ⟨hF, hFne⟩
    · apply d.faceCycle_of_boundaryPath (P := d.path₁)
      · rw [splitFace_faces]; exact Set.mem_insert _ _
      · simp [CellStructure.splitFace]
      · exact d.isPath₁
      · intro σ
        rw [splitFace_sub, d.subRel_face₁_iff]
        rfl
    · apply d.faceCycle_of_boundaryPath (P := d.path₂)
      · rw [splitFace_faces]; exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
      · simp [CellStructure.splitFace, d.face_ne.symm]
      · exact d.isPath₂
      · intro σ
        rw [splitFace_sub, d.subRel_face₂_iff]
        rfl
    · obtain ⟨c⟩ := hcycles.cycle F hF
      have hFc : F ∈ S.cells := S.mem_cells_of_mem_faces hF
      have hF₁ : F ≠ d.face₁ := fun heq => d.face₁_notMem (heq ▸ hFc)
      have hF₂ : F ≠ d.face₂ := fun heq => d.face₂_notMem (heq ▸ hFc)
      have hsubOld : ∀ σ, (S.splitFace d).sub σ F ↔ S.sub σ F := by
        intro σ
        rw [splitFace_sub, subRel_iff_of_mem_cells hS d hFc hFne]
        constructor
        · exact fun h => h.2.2
        · intro h
          refine ⟨hS.sub_mem_left h, ?_, h⟩
          rintro rfl
          exact hFne (hS.face_maximal d.face_mem h)
      have hclosed : S.skel.IsWalk c.target (c.edge :: c.walk) c.target :=
        .cons c.isCycle.isLink.symm c.isCycle.isPath.isWalk
      refine ⟨{
        face_mem := by
          rw [splitFace_faces]
          exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨hF, hFne⟩)
        edge := c.edge
        source := c.source
        target := c.target
        walk := c.walk
        boundary_eq := by
          simp [CellStructure.splitFace, hF₁, hF₂, c.boundary_eq]
        isCycle := ⟨c.isCycle.isLink.mono d.le_skeleton,
          c.isCycle.isPath.mono d.le_skeleton, c.isCycle.notMem⟩
        sub_face := ?_
      }⟩
      intro σ
      rw [hsubOld, c.sub_face, d.pathCells_oldWalk hclosed]

end SplitData

namespace SubdivData

variable (d : S.SubdivData)

/-- A list which is a path in one orientation is a path in every orientation in which the
same ordered edge list is a walk.  The only alternative first orientation can occur for a
single-edge path. -/
theorem isPath_of_isWalk_of_isPath {G : Graph γ γ} {a b x y : γ} {W : List γ}
    (hP : G.IsPath a W b) (hW : G.IsWalk x W y) : G.IsPath x W y := by
  induction hP generalizing x y with
  | nil ha =>
      cases hW with
      | nil hx => exact .nil hx
  | @cons a w b e W hl hP hfresh ih =>
      cases hW with
      | @cons _ w' _ _ _ hl' hW =>
        rcases hl.eq_and_eq_or_eq_and_eq hl' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact .cons hl (ih hW) hfresh
        · have hnil : W = [] := by
            by_contra hne
            obtain ⟨f, hf, hinc⟩ := hW.exists_inc_source hne
            exact hfresh (Graph.mem_walkVertices_of_mem_covered ⟨f, hf, hinc⟩)
          subst W
          cases hW with
          | nil hu => exact Graph.IsPath.single hl.symm (Graph.IsPath.cons_ne hP hfresh).symm

/-- A walk avoiding the subdivided edge visits exactly the same vertices in the subdivided
skeleton. -/
theorem walkVertices_eq_of_notMem {u v : γ} {W : List γ} (h : S.skel.IsWalk u W v)
    (he : d.edge ∉ W) : d.skeleton.walkVertices u W = S.skel.walkVertices u W := by
  apply Set.Subset.antisymm
  · intro z hz
    rcases Graph.mem_walkVertices_iff.1 hz with rfl | ⟨f, hf, y, hl⟩
    · exact Graph.mem_walkVertices_self
    · rw [d.skeleton_isLink] at hl
      rcases hl with ⟨hl, -, -, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact Graph.mem_walkVertices_of_mem_covered ⟨f, hf, y, hl⟩
      · exact (d.newEdge₁_notMem_edgeSet (h.edge_mem hf)).elim
      · exact (d.newEdge₂_notMem_edgeSet (h.edge_mem hf)).elim
  · intro z hz
    rcases Graph.mem_walkVertices_iff.1 hz with rfl | ⟨f, hf, y, hl⟩
    · exact Graph.mem_walkVertices_self
    · apply Graph.mem_walkVertices_of_mem_covered
      refine ⟨f, hf, y, d.skeleton_isLink.2 (Or.inl ⟨hl, ?_, ?_, ?_⟩)⟩
      · exact fun hfe => he (hfe ▸ hf)
      · exact fun hfe => d.newEdge₁_notMem_edgeSet (hfe ▸ hl.edge_mem)
      · exact fun hfe => d.newEdge₂_notMem_edgeSet (hfe ▸ hl.edge_mem)

namespace SubstWalk

variable {d : S.SubdivData} {u v : γ} {W W' : List γ}

/-- Every old visited vertex is still visited after subdivision. -/
theorem old_walkVertices_subset (hsub : d.SubstWalk u W W') :
    S.skel.walkVertices u W ⊆ d.skeleton.walkVertices u W' := by
  induction hsub with
  | nil u => intro z hz; simpa only [Graph.walkVertices_nil] using hz
  | forward hs ih =>
      intro z hz
      rcases Graph.mem_walkVertices_cons d.isLink hz with rfl | hz
      · exact Graph.mem_walkVertices_self
      · have hlink₁ : d.skeleton.IsLink d.newEdge₁ d.left d.newVertex :=
          d.skeleton_isLink.2 (Or.inr (Or.inl ⟨rfl, rfl⟩))
        have hlink₂ : d.skeleton.IsLink d.newEdge₂ d.newVertex d.right :=
          d.skeleton_isLink.2 (Or.inr (Or.inr ⟨rfl, rfl⟩))
        exact Graph.mem_walkVertices_cons_of_mem hlink₁
          (Graph.mem_walkVertices_cons_of_mem hlink₂ (ih hz))
  | backward hs ih =>
      intro z hz
      rcases Graph.mem_walkVertices_cons d.isLink.symm hz with rfl | hz
      · exact Graph.mem_walkVertices_self
      · have hlink₂ : d.skeleton.IsLink d.newEdge₂ d.right d.newVertex :=
          d.skeleton_isLink.2 (Or.inr (Or.inr ⟨rfl, Sym2.eq_swap⟩))
        have hlink₁ : d.skeleton.IsLink d.newEdge₁ d.newVertex d.left :=
          d.skeleton_isLink.2 (Or.inr (Or.inl ⟨rfl, Sym2.eq_swap⟩))
        exact Graph.mem_walkVertices_cons_of_mem hlink₂
          (Graph.mem_walkVertices_cons_of_mem hlink₁ (ih hz))
  | other hl hf hs ih =>
      intro z hz
      rcases Graph.mem_walkVertices_cons hl hz with rfl | hz
      · exact Graph.mem_walkVertices_self
      · have hlink : d.skeleton.IsLink _ _ _ := d.skeleton_isLink.2 (Or.inl
          ⟨hl, hf, fun h => d.newEdge₁_notMem_edgeSet (h ▸ hl.edge_mem),
            fun h => d.newEdge₂_notMem_edgeSet (h ▸ hl.edge_mem)⟩)
        exact Graph.mem_walkVertices_cons_of_mem hlink (ih hz)

/-- A subdivision introduces no visited vertex except the named subdivision vertex. -/
theorem new_walkVertices_subset (hsub : d.SubstWalk u W W') {z : γ}
    (hz : z ∈ d.skeleton.walkVertices u W') :
    z = d.newVertex ∨ z ∈ S.skel.walkVertices u W := by
  induction hsub with
  | nil u => exact Or.inr (by simpa only [Graph.walkVertices_nil] using hz)
  | forward hs ih =>
      have hlink₁ : d.skeleton.IsLink d.newEdge₁ d.left d.newVertex :=
        d.skeleton_isLink.2 (Or.inr (Or.inl ⟨rfl, rfl⟩))
      have hlink₂ : d.skeleton.IsLink d.newEdge₂ d.newVertex d.right :=
        d.skeleton_isLink.2 (Or.inr (Or.inr ⟨rfl, rfl⟩))
      rcases Graph.mem_walkVertices_cons hlink₁ hz with rfl | hz
      · exact Or.inr Graph.mem_walkVertices_self
      · rcases Graph.mem_walkVertices_cons hlink₂ hz with rfl | hz
        · exact Or.inl rfl
        · rcases ih hz with rfl | hz
          · exact Or.inl rfl
          · exact Or.inr (Graph.mem_walkVertices_cons_of_mem d.isLink hz)
  | backward hs ih =>
      have hlink₂ : d.skeleton.IsLink d.newEdge₂ d.right d.newVertex :=
        d.skeleton_isLink.2 (Or.inr (Or.inr ⟨rfl, Sym2.eq_swap⟩))
      have hlink₁ : d.skeleton.IsLink d.newEdge₁ d.newVertex d.left :=
        d.skeleton_isLink.2 (Or.inr (Or.inl ⟨rfl, Sym2.eq_swap⟩))
      rcases Graph.mem_walkVertices_cons hlink₂ hz with rfl | hz
      · exact Or.inr Graph.mem_walkVertices_self
      · rcases Graph.mem_walkVertices_cons hlink₁ hz with rfl | hz
        · exact Or.inl rfl
        · rcases ih hz with rfl | hz
          · exact Or.inl rfl
          · exact Or.inr (Graph.mem_walkVertices_cons_of_mem d.isLink.symm hz)
  | other hl hf hs ih =>
      have hlink : d.skeleton.IsLink _ _ _ := d.skeleton_isLink.2 (Or.inl
        ⟨hl, hf, fun h => d.newEdge₁_notMem_edgeSet (h ▸ hl.edge_mem),
          fun h => d.newEdge₂_notMem_edgeSet (h ▸ hl.edge_mem)⟩)
      rcases Graph.mem_walkVertices_cons hlink hz with rfl | hz
      · exact Or.inr Graph.mem_walkVertices_self
      · rcases ih hz with rfl | hz
        · exact Or.inl rfl
        · exact Or.inr (Graph.mem_walkVertices_cons_of_mem hl hz)

/-- Replacing one edge of a simple path by its two subdivision edges preserves simplicity. -/
theorem isPath (hsub : d.SubstWalk u W W') (hP : S.skel.IsPath u W v) :
    d.skeleton.IsPath u W' v := by
  induction hsub generalizing v with
  | nil u =>
      cases hP with
      | nil hu =>
          exact .nil (by rw [d.skeleton_vertexSet]; exact Set.mem_insert_of_mem _ hu)
  | forward hs ih =>
      cases hP with
      | @cons _ w _ _ _ hl hP hfresh =>
        have hw : d.right = w := d.isLink.right_unique hl
        subst w
        have heW : d.edge ∉ _ :=
          (List.nodup_cons.1 (Graph.IsPath.nodup (Graph.IsPath.cons hl hP hfresh))).1
        have hEq := SubdivData.SubstWalk.eq_of_notMem hs heW
        rw [hEq] at ih ⊢
        have htail := ih hP
        have hverts := d.walkVertices_eq_of_notMem hP.isWalk heW
        have hlink₁ : d.skeleton.IsLink d.newEdge₁ d.left d.newVertex :=
          d.skeleton_isLink.2 (Or.inr (Or.inl ⟨rfl, rfl⟩))
        have hlink₂ : d.skeleton.IsLink d.newEdge₂ d.newVertex d.right :=
          d.skeleton_isLink.2 (Or.inr (Or.inr ⟨rfl, rfl⟩))
        refine .cons hlink₁ (.cons hlink₂ htail ?_) ?_
        · intro hz
          rw [hverts] at hz
          exact d.newVertex_notMem
            (S.mem_cells_of_mem_vertexSet (hP.isWalk.walkVertices_subset hz))
        · intro hz
          rcases Graph.mem_walkVertices_cons hlink₂ hz with hEq | hz
          · exact d.newVertex_notMem (hEq ▸ d.left_mem_cells)
          · apply hfresh
            rw [← hverts]
            exact hz
  | backward hs ih =>
      cases hP with
      | @cons _ w _ _ _ hl hP hfresh =>
        have hw : d.left = w := d.isLink.symm.right_unique hl
        subst w
        have heW : d.edge ∉ _ :=
          (List.nodup_cons.1 (Graph.IsPath.nodup (Graph.IsPath.cons hl hP hfresh))).1
        have hEq := SubdivData.SubstWalk.eq_of_notMem hs heW
        rw [hEq] at ih ⊢
        have htail := ih hP
        have hverts := d.walkVertices_eq_of_notMem hP.isWalk heW
        have hlink₂ : d.skeleton.IsLink d.newEdge₂ d.right d.newVertex :=
          d.skeleton_isLink.2 (Or.inr (Or.inr ⟨rfl, Sym2.eq_swap⟩))
        have hlink₁ : d.skeleton.IsLink d.newEdge₁ d.newVertex d.left :=
          d.skeleton_isLink.2 (Or.inr (Or.inl ⟨rfl, Sym2.eq_swap⟩))
        refine .cons hlink₂ (.cons hlink₁ htail ?_) ?_
        · intro hz
          rw [hverts] at hz
          exact d.newVertex_notMem
            (S.mem_cells_of_mem_vertexSet (hP.isWalk.walkVertices_subset hz))
        · intro hz
          rcases Graph.mem_walkVertices_cons hlink₁ hz with hEq | hz
          · exact d.newVertex_notMem (hEq ▸ d.right_mem_cells)
          · apply hfresh
            rw [← hverts]
            exact hz
  | other hl hf hs ih =>
      cases hP with
      | @cons _ w _ _ _ hl' hP hfresh =>
        have hw : _ = w := hl.right_unique hl'
        subst w
        have htail := ih hP
        have hlink : d.skeleton.IsLink _ _ _ := d.skeleton_isLink.2 (Or.inl
          ⟨hl, hf, fun h => d.newEdge₁_notMem_edgeSet (h ▸ hl.edge_mem),
            fun h => d.newEdge₂_notMem_edgeSet (h ▸ hl.edge_mem)⟩)
        refine .cons hlink htail ?_
        intro hz
        rcases SubdivData.SubstWalk.new_walkVertices_subset hs hz with hEq | hz
        · exact d.newVertex_notMem
            (hEq ▸ S.mem_cells_of_mem_vertexSet hl.left_mem)
        · exact hfresh hz

/-- Every output edge is either one of the two replacement edges or an old input edge. -/
theorem mem_input_of_mem_output (hsub : d.SubstWalk u W W') {x : γ} (hx : x ∈ W') :
    x = d.newEdge₁ ∨ x = d.newEdge₂ ∨ x ∈ W := by
  induction hsub with
  | nil => simp at hx
  | forward hs ih =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · rcases ih hx with h | h | h
        exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (List.mem_cons_of_mem _ h))]
  | backward hs ih =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
      · rcases ih hx with h | h | h
        exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (List.mem_cons_of_mem _ h))]
  | other hl hne hs ih =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Or.inr (Or.inr (List.mem_cons_self ..))
      · rcases ih hx with h | h | h
        exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (List.mem_cons_of_mem _ h))]

/-- Every surviving old input edge occurs in the output. -/
theorem mem_output_of_mem_input_of_ne (hsub : d.SubstWalk u W W') {x : γ}
    (hx : x ∈ W) (hne : x ≠ d.edge) : x ∈ W' := by
  induction hsub with
  | nil => simp at hx
  | forward hs ih =>
      simp only [List.mem_cons] at hx
      rcases hx with h | hx
      · exact absurd h hne
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih hx))
  | backward hs ih =>
      simp only [List.mem_cons] at hx
      rcases hx with h | hx
      · exact absurd h hne
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih hx))
  | other hl hfe hs ih =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih hx)

/-- The removed edge name never occurs in the replacement list. -/
theorem edge_notMem_output (hsub : d.SubstWalk u W W') : d.edge ∉ W' := by
  intro he
  induction hsub with
  | nil => simp at he
  | forward hs ih =>
      simp only [List.mem_cons] at he
      rcases he with h | h | he
      · exact d.newEdge₁_notMem (h ▸ d.edge_mem_cells)
      · exact d.newEdge₂_notMem (h ▸ d.edge_mem_cells)
      · exact ih he
  | backward hs ih =>
      simp only [List.mem_cons] at he
      rcases he with h | h | he
      · exact d.newEdge₂_notMem (h ▸ d.edge_mem_cells)
      · exact d.newEdge₁_notMem (h ▸ d.edge_mem_cells)
      · exact ih he
  | other hl hne hs ih =>
      simp only [List.mem_cons] at he
      rcases he with h | he
      · exact hne h.symm
      · exact ih he

/-- If the old walk crosses the subdivided edge, all three replacement cells occur in the
new path carrier. -/
theorem newCells_subset_pathCells (hsub : d.SubstWalk u W W') (he : d.edge ∈ W) :
    d.newCells ⊆ (S.subdivideEdge d).pathCells u W' := by
  induction hsub with
  | nil => simp at he
  | forward hs ih =>
      intro z hz
      rcases hz with rfl | rfl | rfl
      · exact Or.inr (Graph.mem_walkVertices_cons_of_mem
          (d.skeleton_isLink.2 (Or.inr (Or.inl ⟨rfl, rfl⟩))) Graph.mem_walkVertices_self)
      · exact Or.inl (List.mem_cons_self ..)
      · exact Or.inl (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  | backward hs ih =>
      intro z hz
      rcases hz with rfl | rfl | rfl
      · exact Or.inr (Graph.mem_walkVertices_cons_of_mem
          (d.skeleton_isLink.2 (Or.inr (Or.inr ⟨rfl, Sym2.eq_swap⟩)))
          Graph.mem_walkVertices_self)
      · exact Or.inl (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      · exact Or.inl (List.mem_cons_self ..)
  | other hl hne hs ih =>
      simp only [List.mem_cons] at he
      rcases he with h | he
      · exact absurd h.symm hne
      · intro z hz
        rcases ih he hz with hz | hz
        · exact Or.inl (List.mem_cons_of_mem _ hz)
        · have hlink : d.skeleton.IsLink _ _ _ := d.skeleton_isLink.2 (Or.inl
            ⟨hl, hne, fun h => d.newEdge₁_notMem_edgeSet (h ▸ hl.edge_mem),
              fun h => d.newEdge₂_notMem_edgeSet (h ▸ hl.edge_mem)⟩)
          exact Or.inr (Graph.mem_walkVertices_cons_of_mem hlink hz)

/-- The exact cell-carrier update performed by an orientation-aware subdivision. -/
theorem pathCells_eq (hsub : d.SubstWalk u W W') (hW : S.skel.IsWalk u W v) :
    (S.subdivideEdge d).pathCells u W' =
      {z | (z ∈ S.pathCells u W ∧ z ≠ d.edge) ∨
        (d.edge ∈ W ∧ z ∈ d.newCells)} := by
  ext z
  by_cases he : d.edge ∈ W
  · constructor
    · rintro (hzOut | hz)
      · rcases hsub.mem_input_of_mem_output hzOut with rfl | rfl | hz
        · exact Or.inr ⟨he, Or.inr (Or.inl rfl)⟩
        · exact Or.inr ⟨he, Or.inr (Or.inr rfl)⟩
        · exact Or.inl ⟨Or.inl hz, fun h => hsub.edge_notMem_output (h ▸ hzOut)⟩
      · rcases hsub.new_walkVertices_subset hz with rfl | hz
        · exact Or.inr ⟨he, Or.inl rfl⟩
        · exact Or.inl ⟨Or.inr hz, fun h => Set.disjoint_left.1
            S.disjoint_vertexSet_edgeSet (hW.walkVertices_subset hz) (h ▸ d.edge_mem_edgeSet)⟩
    · rintro (⟨hz, hze⟩ | ⟨-, hz⟩)
      · rcases hz with hz | hz
        · exact Or.inl (hsub.mem_output_of_mem_input_of_ne hz hze)
        · exact Or.inr (hsub.old_walkVertices_subset hz)
      · exact hsub.newCells_subset_pathCells he hz
  · have hEq := SubdivData.SubstWalk.eq_of_notMem hsub he
    have hvertices := d.walkVertices_eq_of_notMem hW he
    constructor
    · rintro (hz | hz)
      · refine Or.inl ⟨Or.inl ?_, ?_⟩
        · rwa [hEq] at hz
        · intro h
          subst z
          exact hsub.edge_notMem_output hz
      · refine Or.inl ⟨Or.inr ?_, ?_⟩
        · rw [subdivideEdge_skel, hEq, hvertices] at hz
          exact hz
        · intro h
          subst z
          rw [subdivideEdge_skel, hEq, hvertices] at hz
          exact Set.disjoint_left.1 S.disjoint_vertexSet_edgeSet
            (hW.walkVertices_subset hz) d.edge_mem_edgeSet
    · rintro (⟨hz, -⟩ | ⟨h, -⟩)
      · rcases hz with hz | hz
        · exact Or.inl (hEq.symm ▸ hz)
        · exact Or.inr (by
            rw [subdivideEdge_skel, hEq, hvertices]
            exact hz)
      · exact absurd h he

/-- Substituting an edge in a cyclic boundary list produces another presentation of a simple
cycle, regardless of which admissible start vertex the boundary data selected. -/
theorem exists_isCycleThrough {e a b : γ} {D : List γ}
    (hsub : d.SubstWalk u (e :: D) W') (hW : S.skel.IsWalk u (e :: D) u)
    (hc : S.skel.IsCycleThrough e a b D) :
    ∃ e' a' D', W' = e' :: D' ∧ d.skeleton.IsCycleThrough e' a' u D' := by
  cases hsub with
  | forward hs =>
      cases hW with
      | @cons _ w _ _ _ hl htail =>
        have hw : d.right = w := d.isLink.right_unique hl
        subst w
        have htailP := SubdivData.isPath_of_isWalk_of_isPath hc.isPath htail
        have htail' := SubdivData.SubstWalk.isPath hs htailP
        have hEq := SubdivData.SubstWalk.eq_of_notMem hs hc.notMem
        rw [hEq] at htail'
        have hverts := d.walkVertices_eq_of_notMem htailP.isWalk hc.notMem
        have hlink₁ : d.skeleton.IsLink d.newEdge₁ d.left d.newVertex :=
          d.skeleton_isLink.2 (Or.inr (Or.inl ⟨rfl, rfl⟩))
        have hlink₂ : d.skeleton.IsLink d.newEdge₂ d.newVertex d.right :=
          d.skeleton_isLink.2 (Or.inr (Or.inr ⟨rfl, rfl⟩))
        have hfresh : d.newVertex ∉ d.skeleton.walkVertices d.right D := by
          intro hz
          rw [hverts] at hz
          exact d.newVertex_notMem
            (S.mem_cells_of_mem_vertexSet (htailP.isWalk.walkVertices_subset hz))
        have hpath : d.skeleton.IsPath d.newVertex (d.newEdge₂ :: D) d.left :=
          .cons hlink₂ htail' hfresh
        have hnot : d.newEdge₁ ∉ d.newEdge₂ :: D := by
          intro hz
          rcases List.mem_cons.1 hz with hz | hz
          · exact d.newEdge_ne hz
          · exact d.newEdge₁_notMem_edgeSet (htailP.edge_mem hz)
        exact ⟨d.newEdge₁, d.newVertex, d.newEdge₂ :: D, by rw [hEq],
          hlink₁.symm, hpath, hnot⟩
  | backward hs =>
      cases hW with
      | @cons _ w _ _ _ hl htail =>
        have hw : d.left = w := d.isLink.symm.right_unique hl
        subst w
        have htailP := SubdivData.isPath_of_isWalk_of_isPath hc.isPath htail
        have htail' := SubdivData.SubstWalk.isPath hs htailP
        have hEq := SubdivData.SubstWalk.eq_of_notMem hs hc.notMem
        rw [hEq] at htail'
        have hverts := d.walkVertices_eq_of_notMem htailP.isWalk hc.notMem
        have hlink₂ : d.skeleton.IsLink d.newEdge₂ d.right d.newVertex :=
          d.skeleton_isLink.2 (Or.inr (Or.inr ⟨rfl, Sym2.eq_swap⟩))
        have hlink₁ : d.skeleton.IsLink d.newEdge₁ d.newVertex d.left :=
          d.skeleton_isLink.2 (Or.inr (Or.inl ⟨rfl, Sym2.eq_swap⟩))
        have hfresh : d.newVertex ∉ d.skeleton.walkVertices d.left D := by
          intro hz
          rw [hverts] at hz
          exact d.newVertex_notMem
            (S.mem_cells_of_mem_vertexSet (htailP.isWalk.walkVertices_subset hz))
        have hpath : d.skeleton.IsPath d.newVertex (d.newEdge₁ :: D) d.right :=
          .cons hlink₁ htail' hfresh
        have hnot : d.newEdge₂ ∉ d.newEdge₁ :: D := by
          intro hz
          rcases List.mem_cons.1 hz with hz | hz
          · exact d.newEdge_ne hz.symm
          · exact d.newEdge₂_notMem_edgeSet (htailP.edge_mem hz)
        exact ⟨d.newEdge₂, d.newVertex, d.newEdge₁ :: D, by rw [hEq],
          hlink₂.symm, hpath, hnot⟩
  | other hl hne hs =>
      cases hW with
      | @cons _ w _ _ _ hl' htail =>
        have hw : _ = w := hl.right_unique hl'
        subst w
        have htailP := SubdivData.isPath_of_isWalk_of_isPath hc.isPath htail
        have htail' := SubdivData.SubstWalk.isPath hs htailP
        have hlink : d.skeleton.IsLink _ _ _ := d.skeleton_isLink.2 (Or.inl
          ⟨hl, hne, fun h => d.newEdge₁_notMem_edgeSet (h ▸ hl.edge_mem),
            fun h => d.newEdge₂_notMem_edgeSet (h ▸ hl.edge_mem)⟩)
        refine ⟨e, _, _, rfl, hlink.symm, htail', ?_⟩
        show e ∉ _
        intro he
        rcases SubdivData.SubstWalk.mem_input_of_mem_output hs he with h | h | h
        · exact d.newEdge₁_notMem (h ▸ S.mem_cells_of_mem_edgeSet hl.edge_mem)
        · exact d.newEdge₂_notMem (h ▸ S.mem_cells_of_mem_edgeSet hl.edge_mem)
        · exact hc.notMem h

end SubstWalk

/-- Edge subdivision preserves cyclic boundaries. -/
theorem boundaryCycles (d : S.SubdivData) (hcycles : S.BoundaryCycles)
    (hS : S.CombInvariants) : (S.subdivideEdge d).BoundaryCycles where
  cycle F hF := by
    rw [subdivideEdge_faces] at hF
    obtain ⟨c⟩ := hcycles.cycle F hF
    obtain ⟨u, hW, hsub⟩ := d.boundary_subst hF
    rw [c.boundary_eq] at hW hsub
    obtain ⟨e', a', D', hlist, hcycle⟩ :=
      SubdivData.SubstWalk.exists_isCycleThrough hsub hW c.isCycle
    have hclosed : S.skel.IsWalk c.target (c.edge :: c.walk) c.target :=
      .cons c.isCycle.isLink.symm c.isCycle.isPath.isWalk
    have hOldCarrier : S.pathCells u (c.edge :: c.walk) =
        S.pathCells c.target (c.edge :: c.walk) :=
      FaceCycle.pathCells_eq_of_perm hW hclosed (.refl _) (by simp) (by simp)
    have hNewCarrier : (S.subdivideEdge d).pathCells u (e' :: D') =
        {z | (z ∈ S.pathCells u (c.edge :: c.walk) ∧ z ≠ d.edge) ∨
          (d.edge ∈ c.edge :: c.walk ∧ z ∈ d.newCells)} := by
      rw [← hlist]
      exact SubdivData.SubstWalk.pathCells_eq hsub hW
    have hedgeList : d.edge ∈ S.pathCells u (c.edge :: c.walk) ↔
        d.edge ∈ c.edge :: c.walk := by
      constructor
      · rintro (he | hv)
        · exact he
        · exact (Set.disjoint_left.1 S.disjoint_vertexSet_edgeSet
            (hW.walkVertices_subset hv) d.edge_mem_edgeSet).elim
      · exact Or.inl
    have hFc : F ∈ S.cells := S.mem_cells_of_mem_faces hF
    have hFe : F ≠ d.edge := S.faces_ne_edgeSet hF d.edge_mem_edgeSet
    refine ⟨{
      face_mem := by rwa [subdivideEdge_faces]
      edge := e'
      source := a'
      target := u
      walk := D'
      boundary_eq := hlist
      isCycle := hcycle
      sub_face := ?_
    }⟩
    intro σ
    rw [subdivideEdge_sub, hNewCarrier]
    change d.subRel σ F ↔ σ = F ∨
      ((σ ∈ S.pathCells u (c.edge :: c.walk) ∧ σ ≠ d.edge) ∨
        (d.edge ∈ c.edge :: c.walk ∧ σ ∈ d.newCells))
    constructor
    · intro h
      rcases h with ⟨-, -, hσe, -, h⟩ | ⟨heq, hnew⟩ | ⟨hσ, hFnew⟩ |
          ⟨hσ, hFnew⟩ | ⟨hσ, hFnew⟩ | ⟨hnew, -, h⟩
      · rcases c.sub_face.1 h with rfl | hcarrier
        · exact Or.inl rfl
        · exact Or.inr (Or.inl ⟨hOldCarrier.symm ▸ hcarrier, hσe⟩)
      · exact absurd (heq ▸ hnew) (SubdivData.notMem_newCells_of_mem_cells hFc)
      · rcases hFnew with rfl | rfl
        exacts [(d.newEdge₁_notMem hFc).elim, (d.newEdge₂_notMem hFc).elim]
      · exact (d.newEdge₁_notMem (hFnew ▸ hFc)).elim
      · exact (d.newEdge₂_notMem (hFnew ▸ hFc)).elim
      · rcases c.sub_face.1 h with hedge | hcarrier
        · exact absurd hedge.symm hFe
        · exact Or.inr (Or.inr ⟨hedgeList.1 (hOldCarrier.symm ▸ hcarrier), hnew⟩)
    · rintro (rfl | (⟨hcarrier, hσe⟩ | ⟨helist, hnew⟩))
      · exact d.subRel_of_old hFc hFc hFe hFe (hS.sub_refl hFc)
      · have hσc : σ ∈ S.cells := CellStructure.pathCells_subset_cells hW hcarrier
        have hsubOld : S.sub σ F := c.sub_face.2
          (Or.inr (hOldCarrier ▸ hcarrier))
        exact d.subRel_of_old hσc hFc hσe hFe hsubOld
      · have hsubEdge : S.sub d.edge F := c.sub_face.2
          (Or.inr (hOldCarrier ▸ hedgeList.2 helist))
        exact (d.newCells_subRel_iff hnew hFc).2 ⟨hFe, hsubEdge⟩

end SubdivData

/-! ### The invariant at every generated stage -/

/-- Every generated structure has cyclic face boundaries once the base structure does. -/
theorem _root_.Schoenflies.GeneratedStructure.boundaryCycles {S₀ S : CellStructure γ}
    (h : GeneratedStructure S₀ S) (hcycles : S₀.BoundaryCycles)
    (h₀ : S₀.CombInvariants) : S.BoundaryCycles := by
  induction h with
  | base => exact hcycles
  | subdivideEdge h d ih => exact d.boundaryCycles ih (h.combInvariants h₀)
  | splitFace h d ih => exact d.boundaryCycles ih (h.combInvariants h₀)

end CellStructure

end Schoenflies
