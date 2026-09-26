/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Iso.GraphIso
public import LeanPool.BrillNoetherGraphs.Utilities.Gluing.TwoEdgeConnectedRigidity

/-!
# Cut conditions under graph isomorphism

The no-bridge cut condition is a property of the underlying multigraph, so
it must be transported across the graph isomorphisms supplied by structural
normal forms.  Keeping this at the graph-isomorphism layer avoids rebuilding
the same finite-cut argument for every presentation theorem.
-/

@[expose] public section

namespace Utilities

open Finset

namespace CFGraphIso

universe u v

variable {G : CFGraph.{u}} {H : CFGraph.{v}} (φ : CFGraphIso G H)

private theorem mem_image_vertexEquiv_iff (S : Finset G.V) (x : G.V) :
    φ.vertexEquiv x ∈ S.image φ.vertexEquiv ↔ x ∈ S := by
  constructor
  · intro h
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp h
    exact φ.vertexEquiv.injective hxy ▸ hy
  · intro hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

private theorem outdeg_S_image (S : Finset G.V) (x : G.V) :
    outdegreeSet H (S.image φ.vertexEquiv) (φ.vertexEquiv x) =
      outdegreeSet G S x := by
  rw [outdeg_S_eq_sum_filter, outdeg_S_eq_sum_filter]
  rw [Finset.sum_filter, Finset.sum_filter]
  rw [← φ.vertexEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : y ∈ S
  · have hImage : φ.vertexEquiv y ∈ S.image φ.vertexEquiv :=
      (φ.mem_image_vertexEquiv_iff S y).mpr hy
    simp [hy, hImage]
  · have hImage : φ.vertexEquiv y ∉ S.image φ.vertexEquiv :=
      (not_congr (φ.mem_image_vertexEquiv_iff S y)).mpr hy
    simp [hy, hImage, φ.map_num_edges]

/-- Cut multiplicity is preserved when a vertex set is carried across a graph
isomorphism. -/
theorem cutMultiplicity_image (S : Finset G.V) :
    cutMultiplicity H (S.image φ.vertexEquiv) = cutMultiplicity G S := by
  unfold cutMultiplicity
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro x hx
    exact φ.outdeg_S_image S x
  · intro x _ y _ hxy
    exact φ.vertexEquiv.injective hxy

/-- The absence-of-bridges cut condition is invariant under graph
isomorphism. -/
theorem twoEdgeCutCondition_map_iff (φ : CFGraphIso G H) :
    TwoEdgeCutCondition H ↔ TwoEdgeCutCondition G := by
  constructor
  · intro hH S hNonempty hProper
    have hImageNonempty : (S.image φ.vertexEquiv).Nonempty :=
      hNonempty.image φ.vertexEquiv
    have hImageProper : S.image φ.vertexEquiv ≠ Finset.univ := by
      intro hAll
      apply hProper
      apply Finset.eq_univ_iff_forall.2
      intro x
      have : φ.vertexEquiv x ∈ S.image φ.vertexEquiv := by rw [hAll]; simp
      exact (φ.mem_image_vertexEquiv_iff S x).mp this
    rw [← φ.cutMultiplicity_image S]
    exact hH _ hImageNonempty hImageProper
  · intro hG S hNonempty hProper
    have hImageNonempty : (S.image φ.vertexEquiv.symm).Nonempty :=
      hNonempty.image φ.vertexEquiv.symm
    have hImageProper : S.image φ.vertexEquiv.symm ≠ Finset.univ := by
      intro hAll
      apply hProper
      apply Finset.eq_univ_iff_forall.2
      intro x
      have : φ.vertexEquiv.symm x ∈ S.image φ.vertexEquiv.symm := by
        rw [hAll]
        simp
      exact (φ.symm.mem_image_vertexEquiv_iff S x).mp this
    rw [← φ.symm.cutMultiplicity_image S]
    exact hG _ hImageNonempty hImageProper

end CFGraphIso

end Utilities
