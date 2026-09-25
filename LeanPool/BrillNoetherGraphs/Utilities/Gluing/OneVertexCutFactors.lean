/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Gluing.VertexCutConnectivity
public import LeanPool.BrillNoetherGraphs.Utilities.Gluing.TwoEdgeConnectedRigidity
public import Mathlib.Tactic

/-!
# Two-edge connectivity of one-vertex-cut factors

Complement symmetry of `cutMultiplicity`, inheritance of the two-edge cut
condition by both factors of a `OneVertexCut`, and the two-vertex lower bound
for positive genus.  Rehomed from `OnceMarkedVertexCutOneFour.lean` (which
imports this file) so that the bridgeless genus-two classification does not
depend on the once-marked census.
-/

@[expose] public section

namespace Utilities

universe u

/-! ## Complement symmetry of cut multiplicity -/

/-- Cut multiplicity counts the edges between a vertex set and its complement,
so it is unchanged by complementation. -/
theorem cutMultiplicity_compl (H : CFGraph.{u}) (S : Finset H.V) :
    cutMultiplicity H S = cutMultiplicity H Sᶜ := by
  classical
  have hLeft : cutMultiplicity H S = ∑ v ∈ S, ∑ w ∈ Sᶜ, (numEdges H v w : ℤ) := by
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [outdeg_S_eq_sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext w
    simp
  have hRight : cutMultiplicity H Sᶜ = ∑ v ∈ Sᶜ, ∑ w ∈ S, (numEdges H v w : ℤ) := by
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [outdeg_S_eq_sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext w
    simp
  rw [hLeft, hRight, Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun v _ => ?_
  rw [num_edges_symmetric]

/-! ## Two-edge connectivity passes to the factors of a one-vertex cut -/

namespace OneVertexCut

variable {K : CFGraph.{u}} (cut : OneVertexCut K)

/-- Membership in the ambient image of a vertex set of the left factor is
membership in the set itself. -/
private theorem mem_image_val_iff (S : Finset cut.leftGraph.V)
    (w : cut.leftGraph.V) : w.val ∈ S.image Subtype.val ↔ w ∈ S := by
  classical
  constructor
  · intro hw
    obtain ⟨a, ha, hEq⟩ := Finset.mem_image.mp hw
    exact (Subtype.ext hEq : a = w) ▸ ha
  · intro hw
    exact Finset.mem_image.mpr ⟨w, hw, rfl⟩

/-- A vertex of the left factor other than the glue has the same outgoing
multiplicity in the factor as its ambient image has out of the ambient image of
the set.  Every ambient edge that could differ runs from a non-glue left vertex
to a non-glue right vertex, and the cut forbids those. -/
private theorem outdeg_S_leftGraph_eq
    (S : Finset cut.leftGraph.V) (hGlue : cut.leftGlue ∉ S)
    (v : cut.leftGraph.V) (hv : v ∈ S) :
    outdegreeSet cut.leftGraph S v = outdegreeSet K (S.image Subtype.val) v.val := by
  classical
  have hMem := cut.mem_image_val_iff S
  have hvGlue : v.val ≠ cut.glue := by
    intro hEq
    exact hGlue ((Subtype.ext hEq : v = cut.leftGlue) ▸ hv)
  set F : K.V → ℤ :=
    fun b => if b ∈ S.image Subtype.val then 0 else (numEdges K v.val b : ℤ)
    with hF
  have hZeroOutside : ∀ b : K.V, b ∉ cut.left → F b = 0 := by
    intro b hb
    have hbRight : b ∈ cut.right := by
      rcases cut.vertex_cover b with h | h
      · exact absurd h hb
      · exact h
    have hbGlue : b ≠ cut.glue := fun hEq => hb (hEq ▸ cut.glue_mem_left)
    have hNum := cut.no_cross v.val v.property hvGlue b hbRight hbGlue
    simp [hF, hNum]
  have hRight : outdegreeSet K (S.image Subtype.val) v.val = ∑ b : K.V, F b := by
    rw [outdeg_S_eq_sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : b ∈ S.image Subtype.val
    · rw [if_neg (fun h => h hb)]
      simp only [hF, if_pos hb]
    · rw [if_pos hb]
      simp only [hF, if_neg hb]
  have hAmbient : ∑ b : K.V, F b = ∑ b ∈ cut.left, F b := by
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun b _ hb => hZeroOutside b hb
  have hUniv : (Finset.univ : Finset cut.leftGraph.V) = cut.left.attach := by
    ext w
    simp only [Finset.mem_univ, true_iff]
    exact Finset.mem_attach _ _
  have hLeft :
      outdegreeSet cut.leftGraph S v = ∑ w ∈ cut.left.attach, F w.val := by
    rw [outdeg_S_eq_sum_filter, Finset.sum_filter, hUniv]
    refine Finset.sum_congr rfl fun w _ => ?_
    have hNum : numEdges cut.leftGraph v w = numEdges K v.val w.val :=
      num_edges_inducedSubgraph K cut.left cut.left_nonempty v w
    by_cases hw : w ∈ S
    · rw [if_neg (fun h => h hw)]
      simp only [hF, if_pos ((hMem w).mpr hw)]
    · rw [if_pos hw, hNum]
      simp only [hF, if_neg (fun h => hw ((hMem w).mp h))]
  rw [hLeft, hRight, hAmbient]
  exact Finset.sum_attach cut.left F

/-- A nonempty vertex set of the left factor avoiding the glue has the same cut
multiplicity as its ambient image. -/
private theorem cutMultiplicity_leftGraph_eq
    (S : Finset cut.leftGraph.V) (hGlue : cut.leftGlue ∉ S) :
    cutMultiplicity cut.leftGraph S =
      cutMultiplicity K (S.image Subtype.val) := by
  classical
  have hImage :
      cutMultiplicity K (S.image Subtype.val) =
        ∑ v ∈ S, outdegreeSet K (S.image Subtype.val) v.val := by
    refine Finset.sum_image ?_
    intro a _ b _ hEq
    exact Subtype.ext hEq
  rw [hImage]
  exact Finset.sum_congr rfl fun v hv =>
    cut.outdeg_S_leftGraph_eq S hGlue v hv

/-- **Two-edge connectivity is inherited by the left factor of a one-vertex
cut.**  No genus, degree, or connectivity hypothesis is needed beyond the
condition on the ambient graph. -/
theorem twoEdgeCutCondition_leftGraph
    (hTwoEdge : TwoEdgeCutCondition K) :
    TwoEdgeCutCondition cut.leftGraph := by
  classical
  have hAway : ∀ S : Finset cut.leftGraph.V, S.Nonempty →
      cut.leftGlue ∉ S → 2 ≤ cutMultiplicity cut.leftGraph S := by
    intro S hNonempty hGlue
    rw [cut.cutMultiplicity_leftGraph_eq S hGlue]
    refine hTwoEdge _ ?_ ?_
    · obtain ⟨w, hw⟩ := hNonempty
      exact ⟨w.val, Finset.mem_image.mpr ⟨w, hw, rfl⟩⟩
    · intro hUniv
      have hGlueMem : cut.glue ∈ S.image Subtype.val := by
        rw [hUniv]
        exact Finset.mem_univ _
      exact hGlue ((cut.mem_image_val_iff S cut.leftGlue).mp hGlueMem)
  intro S hNonempty hProper
  by_cases hGlue : cut.leftGlue ∈ S
  · have hComplNonempty : (Sᶜ : Finset cut.leftGraph.V).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hEmpty
      exact hProper ((Finset.compl_eq_empty_iff S).mp hEmpty)
    have hComplGlue : cut.leftGlue ∉ (Sᶜ : Finset cut.leftGraph.V) := by
      simp [hGlue]
    rw [cutMultiplicity_compl]
    exact hAway _ hComplNonempty hComplGlue
  · exact hAway S hNonempty hGlue

/-- Two-edge connectivity is inherited by the right factor as well. -/
theorem twoEdgeCutCondition_rightGraph
    (hTwoEdge : TwoEdgeCutCondition K) :
    TwoEdgeCutCondition cut.rightGraph :=
  cut.swap.twoEdgeCutCondition_leftGraph hTwoEdge

end OneVertexCut

/-! ## Rigidity of a genus-one factor -/

/-- A graph of positive genus has at least two vertices: a single vertex
carries no edge, since chip-firing graphs are loopless. -/
theorem exists_vertex_ne_of_genus_pos {H : CFGraph.{u}} (y : H.V)
    (hGenus : 0 < genus H) : ∃ p : H.V, p ≠ y := by
  by_contra hNone
  push Not at hNone
  have hEdges : H.edges = 0 := by
    rw [Multiset.eq_zero_iff_forall_notMem]
    intro e hEdge
    have h1 := hNone e.1
    have h2 := hNone e.2
    have hLoop : e = (y, y) := by
      rcases e with ⟨a, b⟩
      simp_all
    rw [hLoop] at hEdge
    exact H.loopless y hEdge
  have hCard : 0 < Fintype.card H.V := Fintype.card_pos
  have hValue : genus H = 0 - (Fintype.card H.V : ℤ) + 1 := by
    unfold genus
    rw [hEdges]
    simp
  omega

end Utilities
