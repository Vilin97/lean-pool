/-
Copyright (c) 2026 ukiyois, OpenCode agent sessions. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ukiyois, OpenCode agent sessions
-/
module

public import LeanPool.HardSphereNBC.HardSphereTreeDifference


/-!
# HardSphereTreeEdges

Graph, coordinate, and measure constructions for the hard-sphere NBC volume identity.
-/

@[expose] public section

namespace HsVirial

open Set
open Metric
open SimpleGraph
open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The tree edge selected by the rooted parent of a free vertex. -/
def hardSphereTreeParentEdge {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k))
    (i : Fin (k - 1)) : Sym2 (Fin k) :=
  s(hardSphereTreeParent hT i, hardSphereFreeParticleIndex i)

lemma hardSphereTreeParentEdge_mem {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k))
    (i : Fin (k - 1)) :
    hardSphereTreeParentEdge hT i ∈ T := by
  exact hardSphereTreeParent_mem hT i

lemma hardSphereTreeParentEdge_injective {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k)) :
    Function.Injective (hardSphereTreeParentEdge hT) := by
  intro i j hij
  by_contra hne
  have hij' :
      s(hardSphereTreeParent hT i, hardSphereFreeParticleIndex i) =
        s(hardSphereTreeParent hT j, hardSphereFreeParticleIndex j) := hij
  rcases (Sym2.eq_iff.mp hij') with hsame | hcross
  · exact hne (Fin.ext (by
      have hval := congrArg Fin.val hsame.2
      simpa [hardSphereFreeParticleIndex] using hval))
  · have hi := hardSphereTreeParent_dist_succ hT i
    have hj := hardSphereTreeParent_dist_succ hT j
    rw [hcross.1] at hi
    rw [hcross.2] at hi
    rw [← hcross.2] at hi
    rw [← hcross.2] at hj
    omega

/-- The edges joining each free particle to its rooted-tree parent. -/
def hardSphereTreeParentEdgeFinset {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k)) : Finset (Sym2 (Fin k)) :=
  Finset.univ.image (hardSphereTreeParentEdge hT)

lemma hardSphereTreeParentEdgeFinset_subset {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k)) :
    hardSphereTreeParentEdgeFinset hT ⊆ T := by
  intro e he
  rcases Finset.mem_image.mp he with ⟨i, hi, rfl⟩
  exact hardSphereTreeParentEdge_mem hT i

lemma hardSphereTreeParentEdgeFinset_card {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k)) :
    (hardSphereTreeParentEdgeFinset hT).card = k - 1 := by
  classical
  unfold hardSphereTreeParentEdgeFinset
  rw [Finset.card_image_of_injective _ (hardSphereTreeParentEdge_injective hT)]
  simp

lemma hardSphereTreeEdgeFinset_eq {k : Nat}
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k)) :
    graphEdgeFinset (hardSphereTreeGraph T) = T := by
  classical
  have hground : (T : Set (Sym2 (Fin k))) ⊆
      (completeGraph (Fin k)).edgeSet := by
    intro e he
    exact mem_graphEdgeFinset.mp
      ((Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1) he)
  unfold hardSphereTreeGraph
  exact graphEdgeFinset_fromEdgeSet hground

lemma hardSphereTreeEdgeFinset_card {k : Nat} {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k)) :
    T.card = k - 1 := by
  let : Fintype (hardSphereTreeGraph T).edgeSet := Fintype.ofFinite _
  have hcard := (hardSphereTreeGraph_isTree hT).card_edgeFinset
  have hnative : graphEdgeFinset (hardSphereTreeGraph T) =
      (hardSphereTreeGraph T).edgeFinset := by
    apply Finset.coe_injective
    simp
  rw [← hnative, hardSphereTreeEdgeFinset_eq hT] at hcard
  have hcard' : T.card + 1 = k := by simpa using hcard
  omega

lemma hardSphereTreeParentEdgeFinset_eq {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k)) :
    hardSphereTreeParentEdgeFinset hT = T := by
  apply Finset.eq_of_subset_of_card_le (hardSphereTreeParentEdgeFinset_subset hT)
  rw [hardSphereTreeParentEdgeFinset_card hT, hardSphereTreeEdgeFinset_card hT]

lemma hardSphereTreeRegion_eq_flatDifferencePreimage {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k)) :
    hardSphereTreeRegion T =
      (fun r => hardSphereTreeFlatDifferenceLinearMap hT
        (hardSphereCoordinateEquiv k r)) ⁻¹'
        hardSphereFlatProductBallRegion (k - 1) := by
  apply Set.Subset.antisymm
  · exact hardSphereTreeRegion_subset_flatDifferencePreimage hT
  · intro r hr
    change ∀ e ∈ T, hardSphereActiveExact r e = true
    intro e he
    have he' : e ∈ hardSphereTreeParentEdgeFinset hT := by
      rw [hardSphereTreeParentEdgeFinset_eq hT]
      exact he
    rcases Finset.mem_image.mp he' with ⟨i, hi, hiedge⟩
    have hblock : (fun a =>
        hardSphereTreeFlatDifferenceLinearMap hT
          (hardSphereCoordinateEquiv k r) (i, a)) =
        (fun a => hardSphereTreeDifference hT r i a) :=
      hardSphereTreeDifferenceFlatBlock_eq hT r i
    change hardSphereTreeFlatDifferenceLinearMap hT
        (hardSphereCoordinateEquiv k r) ∈
      hardSphereFlatProductBallRegion (k - 1) at hr
    have hball : (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))
        (fun a => hardSphereTreeFlatDifferenceLinearMap hT
          (hardSphereCoordinateEquiv k r) (i, a)) ∈
        Metric.ball (0 : HSPosition 3) 1 := hr i
    have hnorm' : ‖(MeasurableEquiv.toLp 2 (Fin 3 → ℝ))
        (fun a => hardSphereTreeFlatDifferenceLinearMap hT
          (hardSphereCoordinateEquiv k r) (i, a))‖ < (1 : ℝ) := by
      simpa [mem_ball_iff_norm] using hball
    have hnorm : ‖hardSphereTreeDifference hT r i‖ < (1 : ℝ) := by
      rw [hblock] at hnorm'
      simpa using hnorm'
    rw [← hiedge]
    change hardSphereActiveExact r
      s(hardSphereTreeParent hT i, hardSphereFreeParticleIndex i) = true
    rw [hardSphereActiveExact_mk]
    have hnorm_rev : ‖hardSpherePosition r
        (hardSphereTreeParent hT i) -
        hardSpherePosition r (hardSphereFreeParticleIndex i)‖ < (1 : ℝ) := by
      simpa [hardSphereTreeDifference, norm_sub_rev] using hnorm
    exact decide_eq_true_eq.mpr hnorm_rev

end

end HsVirial
