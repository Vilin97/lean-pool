/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.GeneratedStructure
public import LeanPool.Schoenflies.FaceCyclesProof

/-!
# Cyclic boundaries of abstract 2-cells

The abstract `CellStructure.boundary` field is only a list of edge names.  The finite-transfer
construction needs the stronger invariant that each face boundary is a simple cycle and that
its vertices and edges are exactly the strict subcells of the face.  This module packages that
invariant in the representation already used by `Graph.IsLongCycle`.

The distinguished edge `edge` closes the simple detour `walk`.  The list `edge :: walk` is a
closed walk when started at `target`: it crosses the distinguished edge backwards to `source`
and follows the detour back to `target`.  Two-edge cycles are allowed: an ear split can
legitimately create a digon even when the initial outer cycle has at least three vertices.
Stating the carrier clause with
`CellStructure.pathCells` makes it directly comparable with `SplitData.sub_face`.

## Blueprint

* `Schoenflies.CellStructure.FaceCycle`, `BoundaryCycles` — the maintained form of the
  sentence in `lem:cellulation-invariants` that the cells below every 2-cell form its boundary
  cycle.
-/

@[expose] public section

open Set
open scoped Graph

namespace Schoenflies

namespace CellStructure

variable {γ : Type*}

/-- A face boundary is a simple cycle, and its carrier is exactly the face's strict subcells.
This is data rather than a proposition because the finite-transfer step extracts its named
edge, vertices and complementary path. -/
structure FaceCycle (S : CellStructure γ) (F : γ) where
  /-- The indexed cell is a face of the structure. -/
  face_mem : F ∈ S.faces
  /-- A distinguished edge of the boundary cycle. -/
  edge : γ
  /-- One end of the distinguished edge and the source of the complementary path. -/
  source : γ
  /-- The other end, at which the displayed closed boundary list starts. -/
  target : γ
  /-- The complementary path from `source` to `target`. -/
  walk : List γ
  /-- The raw boundary datum is the distinguished edge followed by the complementary path. -/
  boundary_eq : S.boundary F = edge :: walk
  /-- The distinguished edge and complementary path form a simple cycle. -/
  isCycle : S.skel.IsCycleThrough edge source target walk
  /-- The face itself and the cells of the cycle are exactly the cells below the face. -/
  sub_face : ∀ ⦃σ⦄, S.sub σ F ↔
    σ = F ∨ σ ∈ S.pathCells target (edge :: walk)

/-- The two simple boundary paths obtained by cutting a face cycle at distinct vertices.
Its last two fields are deliberately identical to `SplitData.sub_face` and
`SplitData.paths_meet`, so an ear insertion can copy the data without translation. -/
structure BoundaryPaths (S : CellStructure γ) (F a b : γ) where
  /-- The first boundary path from `a` to `b`. -/
  path₁ : List γ
  /-- The complementary boundary path. -/
  path₂ : List γ
  /-- The first list is a simple path in the skeleton. -/
  isPath₁ : S.skel.IsPath a path₁ b
  /-- The second list is a simple path in the skeleton. -/
  isPath₂ : S.skel.IsPath a path₂ b
  /-- The face and the cells of the two paths are exactly the cells below the face. -/
  sub_face : ∀ ⦃σ⦄, S.sub σ F ↔
    σ = F ∨ σ ∈ S.pathCells a path₁ ∪ S.pathCells a path₂
  /-- The paths meet only at their two endpoints. -/
  paths_meet : S.pathCells a path₁ ∩ S.pathCells a path₂ = {a, b}

/-- Every 2-cell of an abstract structure admits simple boundary-cycle data.  This is a
proposition so that membership proofs remain proof-irrelevant; `BoundaryCycles.faceCycle`
chooses the exported data once and for all. -/
structure BoundaryCycles (S : CellStructure γ) : Prop where
  /-- Existence of boundary-cycle data for each face. -/
  cycle : ∀ F, F ∈ S.faces → Nonempty (S.FaceCycle F)

namespace BoundaryCycles

variable {S : CellStructure γ}

/-- The chosen simple boundary cycle of a face. -/
noncomputable def faceCycle (h : S.BoundaryCycles) (F : γ) (hF : F ∈ S.faces) :
    S.FaceCycle F :=
  Classical.choice (h.cycle F hF)

end BoundaryCycles

namespace FaceCycle

variable {S : CellStructure γ} {F : γ}

/-- The boundary list is a closed walk, in the orientation recorded by `boundary_eq`. -/
theorem isWalk (h : S.FaceCycle F) : S.skel.IsWalk h.target (S.boundary F) h.target := by
  rw [h.boundary_eq]
  exact .cons h.isCycle.isLink.symm h.isCycle.isPath.isWalk

/-- Every cell of the displayed boundary cycle is a strict subcell of its face. -/
theorem sub_of_mem_pathCells (h : S.FaceCycle F) {σ : γ}
    (hσ : σ ∈ S.pathCells h.target (h.edge :: h.walk)) : S.sub σ F :=
  h.sub_face.2 (Or.inr hσ)

/-- Path cells split over the concatenation of two composable walks. -/
theorem pathCells_append {u w v : γ} {W₁ W₂ : List γ}
    (h₁ : S.skel.IsWalk u W₁ w) (h₂ : S.skel.IsWalk w W₂ v) :
    S.pathCells u (W₁ ++ W₂) = S.pathCells u W₁ ∪ S.pathCells w W₂ := by
  apply Set.Subset.antisymm
  · rintro σ (hσ | hσ)
    · rcases List.mem_append.1 hσ with hσ | hσ
      · exact Or.inl (Or.inl hσ)
      · exact Or.inr (Or.inl hσ)
    · rcases Graph.walkVertices_append_subset hσ with hσ | hσ
      · exact Or.inl (Or.inr hσ)
      · exact Or.inr (Or.inr hσ)
  · rintro σ (hσ | hσ)
    · rcases hσ with hσ | hσ
      · exact Or.inl (List.mem_append_left W₂ hσ)
      · exact Or.inr (Graph.walkVertices_mono (List.subset_append_left W₁ W₂) hσ)
    · rcases hσ with hσ | hσ
      · exact Or.inl (List.mem_append_right W₁ hσ)
      · rcases Graph.mem_walkVertices_iff.1 hσ with rfl | hcov
        · exact Or.inr
            (Graph.walkVertices_mono (List.subset_append_left W₁ W₂)
              h₁.target_mem_walkVertices)
        · exact Or.inr (Graph.mem_walkVertices_of_mem_covered
            (Graph.coveredVertices_append.symm ▸ Or.inr hcov))

/-- Reversing a walk changes neither its edge cells nor its vertex cells. -/
theorem pathCells_reverse {u v : γ} {W : List γ} (h : S.skel.IsWalk u W v) :
    S.pathCells v W.reverse = S.pathCells u W := by
  rw [CellStructure.pathCells, CellStructure.pathCells, h.reverse_walkVertices]
  simp

/-- Nonempty walks with permuted edge lists have the same path cells. -/
theorem pathCells_eq_of_perm {u₁ v₁ u₂ v₂ : γ} {W₁ W₂ : List γ}
    (h₁ : S.skel.IsWalk u₁ W₁ v₁) (h₂ : S.skel.IsWalk u₂ W₂ v₂)
    (hp : W₁.Perm W₂) (hne₁ : W₁ ≠ []) (hne₂ : W₂ ≠ []) :
    S.pathCells u₁ W₁ = S.pathCells u₂ W₂ := by
  rw [CellStructure.pathCells, CellStructure.pathCells,
    h₁.walkVertices_eq_covered hne₁, h₂.walkVertices_eq_covered hne₂]
  ext σ
  simp only [Set.mem_union, Set.mem_ofPred_eq, Graph.mem_coveredVertices_iff]
  constructor
  · rintro (hσ | ⟨e, he, hi⟩)
    · exact Or.inl (hp.mem_iff.1 hσ)
    · exact Or.inr ⟨e, hp.mem_iff.1 he, hi⟩
  · rintro (hσ | ⟨e, he, hi⟩)
    · exact Or.inl (hp.mem_iff.2 hσ)
    · exact Or.inr ⟨e, hp.mem_iff.2 he, hi⟩

/-- A vertex below a cyclic face lies on the complementary path used to present the cycle. -/
theorem mem_walk_of_vertex_sub (h : S.FaceCycle F) {a : γ} (ha : a ∈ V(S.skel))
    (haF : S.sub a F) : a ∈ S.skel.walkVertices h.source h.walk := by
  rcases h.sub_face.1 haF with rfl | haC
  · exact absurd ha (Set.disjoint_left.1 S.disjoint_faces_vertexSet h.face_mem)
  rcases haC with haE | haV
  · have hclosed : S.skel.IsWalk h.target (h.edge :: h.walk) h.target :=
      .cons h.isCycle.isLink.symm h.isCycle.isPath.isWalk
    exact (Set.disjoint_left.1 S.disjoint_vertexSet_edgeSet ha (hclosed.edge_mem haE)).elim
  · rcases Graph.mem_walkVertices_cons h.isCycle.isLink.symm haV with rfl | haW
    · exact h.isCycle.isPath.target_mem_walkVertices
    · exact haW

/-- Cutting a cyclic face at two distinct boundary vertices gives the two pieces required by
`SplitData`.  The second path returned by `Graph.IsCycleThrough.split_at` is reversed so that
both displayed paths run from `a` to `b`. -/
theorem boundaryPaths (h : S.FaceCycle F) {a b : γ} (ha : a ∈ V(S.skel))
    (hb : b ∈ V(S.skel)) (haF : S.sub a F) (hbF : S.sub b F) (hab : a ≠ b) :
    Nonempty (S.BoundaryPaths F a b) := by
  have haW := h.mem_walk_of_vertex_sub ha haF
  have hbW := h.mem_walk_of_vertex_sub hb hbF
  obtain ⟨D₁, D₂, h₁, h₂, hperm, hmeet⟩ :=
    h.isCycle.split_at haW hbW hab
  have hnodup : (h.edge :: h.walk).Nodup :=
    List.nodup_cons.2 ⟨h.isCycle.notMem, h.isCycle.isPath.nodup⟩
  have hdisj : ∀ g ∈ D₁, g ∉ D₂ := fun g hg₁ hg₂ =>
    (List.nodup_append.1 (hperm.nodup_iff.2 hnodup)).2.2 g hg₁ g hg₂ rfl
  have hclosed : S.skel.IsWalk h.target (h.edge :: h.walk) h.target :=
    .cons h.isCycle.isLink.symm h.isCycle.isPath.isWalk
  have hcarrier : S.pathCells a D₁ ∪ S.pathCells a D₂.reverse =
      S.pathCells h.target (h.edge :: h.walk) := by
    calc
      S.pathCells a D₁ ∪ S.pathCells a D₂.reverse =
          S.pathCells a D₁ ∪ S.pathCells b D₂ := by
            rw [pathCells_reverse h₂.isWalk]
      _ = S.pathCells a (D₁ ++ D₂) := (pathCells_append h₁.isWalk h₂.isWalk).symm
      _ = S.pathCells h.target (h.edge :: h.walk) :=
        pathCells_eq_of_perm (h₁.isWalk.append h₂.isWalk) hclosed hperm
          (List.append_ne_nil_of_left_ne_nil (h₁.ne_nil hab) D₂) (by simp)
  have hinter : S.pathCells a D₁ ∩ S.pathCells a D₂.reverse = {a, b} := by
    apply Set.Subset.antisymm
    · rintro σ ⟨hσ₁, hσ₂⟩
      have hσ₂' : σ ∈ S.pathCells b D₂ := by
        rw [← pathCells_reverse h₂.isWalk]
        exact hσ₂
      rcases hσ₁ with he₁ | hv₁
      · rcases hσ₂' with he₂ | hv₂
        · exact (hdisj σ he₁ he₂).elim
        · exact (Set.disjoint_left.1 S.disjoint_vertexSet_edgeSet
            (h₂.isWalk.walkVertices_subset hv₂) (h₁.edge_mem he₁)).elim
      · rcases hσ₂' with he₂ | hv₂
        · exact (Set.disjoint_left.1 S.disjoint_vertexSet_edgeSet
            (h₁.isWalk.walkVertices_subset hv₁) (h₂.edge_mem he₂)).elim
        · exact hmeet σ hv₁ hv₂
    · rintro σ (rfl | rfl)
      · exact ⟨Or.inr Graph.mem_walkVertices_self, Or.inr Graph.mem_walkVertices_self⟩
      · exact ⟨Or.inr h₁.target_mem_walkVertices,
          Or.inr h₂.reverse.target_mem_walkVertices⟩
  exact ⟨{
    path₁ := D₁
    path₂ := D₂.reverse
    isPath₁ := h₁
    isPath₂ := h₂.reverse
    sub_face := by intro σ; rw [h.sub_face, hcarrier]
    paths_meet := hinter
  }⟩

end FaceCycle

namespace BoundaryCycles

variable {S : CellStructure γ}

/-- The two chosen boundary paths between distinct vertices of a cyclic face. -/
noncomputable def boundaryPaths (h : S.BoundaryCycles) (F : γ) (hF : F ∈ S.faces)
    (a b : γ) (ha : a ∈ V(S.skel)) (hb : b ∈ V(S.skel))
    (haF : S.sub a F) (hbF : S.sub b F) (hab : a ≠ b) : S.BoundaryPaths F a b :=
  Classical.choice ((h.faceCycle F hF).boundaryPaths ha hb haF hbF hab)

end BoundaryCycles

end CellStructure

end Schoenflies
