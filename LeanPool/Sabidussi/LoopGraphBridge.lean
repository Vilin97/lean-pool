/-
Copyright (c) 2026 Nikolay Ulyanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolay Ulyanov
-/
import LeanPool.Sabidussi.LoopMultigraph
import LeanPool.Sabidussi.CyclicWord

/-!
# From a cyclic word back to a loop-capable endpoint multigraph

The letters are transition vertices and the gaps are labelled edge objects.  Cyclic-word side
zero denotes the preceding gap, while Euler-tour side zero denotes the current departing
half-edge; the bridge therefore precomposes occurrence sides with `Fin.rev`.
-/

namespace Sabidussi
namespace LoopMultigraph

set_option backward.isDefEq.respectTransparency false

open Sabidussi
open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  {G : LoopMultigraph V E}

/-- The cyclic transition word read from an Euler tour. -/
def EulerTour.eulerWord (T : G.EulerTour) : Sabidussi.CyclicWord.Word (V := V) where
  n := T.n
  letter := T.vertexAt

namespace EulerTour

variable (T : G.EulerTour)

omit [DecidableEq E] [DecidableEq V] in
@[simp]
theorem eulerWord_letter (i : T.Pos) : T.eulerWord.letter i = T.vertexAt i := rfl

omit [DecidableEq E] [DecidableEq V] in
@[simp]
theorem eulerWord_prev (i : T.Pos) : T.eulerWord.prev i = T.prev i := rfl

/-- Reversal is an equivalence on the two transition sides. -/
private def revFinTwoEquiv : Fin 2 ≃ Fin 2 :=
  Fin.rev_involutive.toPerm

/-- Occurrence sides with the cyclic-word convention are exactly the incident half-edges. -/
def wordOccurrenceSideEquivHalfEdgesAt (v : V) :
    T.eulerWord.Occurrence v × Fin 2 ≃ G.halfEdgesAt v :=
  (Equiv.prodCongr (Equiv.refl _) revFinTwoEquiv).trans
    (T.occurrenceSideEquivHalfEdgesAt v)

omit [DecidableEq E] [DecidableEq V] in
/-- Under the preceding equivalence, the gap incident with a word-occurrence side is the edge
underlying the corresponding half-edge. -/
theorem incidentColor_eq_halfEdgeColor
    (x : T.eulerWord.Pos → Color) {v : V}
    (os : T.eulerWord.Occurrence v × Fin 2) :
    T.eulerWord.incidentColor x os.1 os.2 =
      x (T.edge.symm ((T.wordOccurrenceSideEquivHalfEdgesAt v os).1.1)) := by
  rcases os with ⟨o, s⟩
  fin_cases s
  · change x (T.prev o.1) = x (T.edge.symm (T.edge (T.prev o.1)))
    simp
  · change x o.1 = x (T.edge.symm (T.edge o.1))
    simp

/-- The coloured occurrence sides of the word and the correspondingly coloured half-edges at a
vertex are equinumerous. -/
def coloredOccurrenceSideEquivColoredHalfEdgesAt
    (C : T.eulerWord.Coloring) (v : V) (z : Color) :
    {os : T.eulerWord.Occurrence v × Fin 2 //
      T.eulerWord.incidentColor C.color os.1 os.2 = z} ≃
    {h : G.halfEdgesAt v // C.color (T.edge.symm h.1.1) = z} :=
  (T.wordOccurrenceSideEquivHalfEdgesAt v).subtypeEquiv fun os ↦ by
    rw [T.incidentColor_eq_halfEdgeColor C.color os]

omit [DecidableEq E] in
private theorem sum_support_edgeIncidence_eq_sum_halfEdgesAt
    (color : E → Color) (z : Color) (v : V) :
    (∑ e ∈ (Finset.univ.filter fun e ↦ color e = z), G.edgeIncidence v e) =
      ∑ h : G.halfEdgesAt v, if color h.1.1 = z then 1 else 0 := by
  change (∑ e ∈ (Finset.univ.filter fun e ↦ color e = z), G.edgeIncidence v e) =
    ∑ h : {h : HalfEdge E // G.vertex h = v}, if color h.1.1 = z then 1 else 0
  rw [← Finset.sum_subtype (Finset.univ.filter fun h : HalfEdge E ↦ G.vertex h = v)
    (by simp) (fun h : HalfEdge E ↦ if color h.1 = z then (1 : F₂) else 0)]
  rw [Finset.sum_filter]
  rw [Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  apply Fintype.sum_congr
  intro e
  rw [Fin.sum_univ_two]
  by_cases he : color e = z <;> simp [edgeIncidence, vertex, he]

omit [DecidableEq E] in
private theorem isEvenEdgeSet_of_coloredHalfEdgesAt_even
    (color : E → Color)
    (heven : ∀ (v : V) (z : Color),
      Even (Fintype.card {h : G.halfEdgesAt v // color h.1.1 = z})) (z : Color) :
    G.IsEvenEdgeSet (Finset.univ.filter fun e ↦ color e = z) := by
  intro v
  rw [sum_support_edgeIncidence_eq_sum_halfEdgesAt color z v]
  rw [Finset.sum_boole]
  rw [← Fintype.card_subtype]
  exact ZMod.natCast_eq_zero_iff_even.mpr (heven v z)

/-- A cyclic-word colouring gives the graph-theoretic compatible four-colouring certificate. -/
noncomputable def compatibleFourColoringOfWordColoring
    (C : T.eulerWord.Coloring) : G.CompatibleFourColoring T where
  color := fun e ↦ C.color (T.edge.symm e)
  transition_ne := by
    intro i
    simpa using C.transition_ne i
  color_even := by
    apply isEvenEdgeSet_of_coloredHalfEdgesAt_even
    intro v z
    rw [← Fintype.card_congr (T.coloredOccurrenceSideEquivColoredHalfEdgesAt C v z)]
    exact C.color_even v z

end EulerTour

/-- Sabidussi compatibility for finite endpoint multigraphs, including loops. -/
theorem loop_sabidussi_compatibility (T : G.EulerTour)
    (hmin : ∀ v : V, 4 ≤ G.degree v) :
    ∃ S : G.CircuitDecomposition, S.Compatible T := by
  have hword : ∀ v : V, 2 ≤ Fintype.card (T.eulerWord.Occurrence v) := by
    intro v
    let e : T.eulerWord.Occurrence v ≃ T.Occurrence v := Equiv.refl _
    rw [Fintype.card_congr e]
    have hd := hmin v
    rw [T.degree_eq_two_mul_card_occurrence v] at hd
    omega
  obtain ⟨C⟩ := T.eulerWord.exists_coloring hword
  exact (T.compatibleFourColoringOfWordColoring C).exists_compatible_circuit_decomposition

end LoopMultigraph
end Sabidussi
