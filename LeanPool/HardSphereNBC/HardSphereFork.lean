/-
Copyright (c) 2026 ukiyois, OpenCode agent sessions. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ukiyois, OpenCode agent sessions
-/
import LeanPool.HardSphereNBC.HardSphereMeasure
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! ### Concrete tree and fork regions -/

namespace HsVirial

open Set
open Metric
open SimpleGraph
open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- An order-compatible fork `(a,b,c)` with `a < b < c`; `a` is its center and
`b,c` are its two leaves. -/
def hardSphereFork {k : Nat} (T : Finset (Sym2 (Fin k)))
    (a b c : Fin k) : Prop :=
  a < b ∧ b < c ∧ s(a, b) ∈ T ∧ s(a, c) ∈ T

lemma hardSphereEdgeLE_fork_chord {k : Nat} {a b c : Fin k}
    (hab : a < b) (hbc : b < c) :
    graphEdgeLE s(a, b) s(b, c) := by
  change hardSphereEdgeKey (s(a, b)) ≤ hardSphereEdgeKey (s(b, c))
  simp only [hardSphereEdgeKey, Sym2.inf_mk, Sym2.sup_mk]
  simp only [min_eq_left hab.le, max_eq_right hab.le,
    min_eq_left hbc.le, max_eq_right hbc.le]
  rw [Prod.Lex.toLex_le_toLex]
  exact Or.inl hab

lemma hardSphereEdgeLE_fork_member {k : Nat} {a b c : Fin k}
    (hab : a < b) (hbc : b < c) :
    graphEdgeLE s(a, c) s(b, c) := by
  change hardSphereEdgeKey (s(a, c)) ≤ hardSphereEdgeKey (s(b, c))
  simp only [hardSphereEdgeKey, Sym2.inf_mk, Sym2.sup_mk]
  have hac : a < c := lt_trans hab hbc
  simp only [min_eq_left hac.le, max_eq_right hac.le,
    min_eq_left hbc.le, max_eq_right hbc.le]
  rw [Prod.Lex.toLex_le_toLex]
  exact Or.inl hab

lemma isGraphForest_of_card_le_two
    {V : Type*} [Fintype V] {G : SimpleGraph V} {A : Finset (Sym2 V)}
    (hA : A ⊆ graphEdgeFinset G) (hcard : A.card ≤ 2) :
    IsGraphForest G A := by
  classical
  refine ⟨?_, ?_⟩
  · intro e he
    exact mem_graphEdgeFinset.mp (hA he)
  rw [SimpleGraph.isAcyclic_iff_free_cycleGraph]
  intro n hn hcontained
  obtain ⟨v, c, hc, hlen⟩ :=
    (SimpleGraph.cycleGraph_isContained_iff hn).mp hcontained
  have hsub : cycleEdgeFinset c ⊆ A := by
    intro e he
    have he' : e ∈ (SimpleGraph.fromEdgeSet (A : Set (Sym2 V))).edgeSet := by
      apply c.edges_subset_edgeSet
      simpa [cycleEdgeFinset] using he
    rw [SimpleGraph.edgeSet_fromEdgeSet] at he'
    exact he'.1
  have hcard' := Finset.card_le_card hsub
  rw [cycleEdgeFinset_card hc, hlen] at hcard'
  omega

lemma isGraphTriangleCircuit
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (habG : s(a, b) ∈ G.edgeSet)
    (hacG : s(a, c) ∈ G.edgeSet)
    (hbcG : s(b, c) ∈ G.edgeSet) :
    IsGraphCircuit G {s(a, b), s(a, c), s(b, c)} := by
  let C : Finset (Sym2 V) := {s(a, b), s(a, c), s(b, c)}
  have hCground : C ⊆ graphEdgeFinset G := by
    intro e he
    simp only [C, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact mem_graphEdgeFinset.mpr habG
    · exact mem_graphEdgeFinset.mpr hacG
    · exact mem_graphEdgeFinset.mpr hbcG
  have hCcard : C.card = 3 := by
    simp [C, hab, hac, hbc]
  have hnotforest : ¬IsGraphForest G C := by
    intro hforest
    let H := SimpleGraph.fromEdgeSet (C : Set (Sym2 V))
    have habH : H.Adj a b := by
      rw [SimpleGraph.fromEdgeSet_adj]
      constructor
      · simp [C]
      · exact hab
    have hbcH : H.Adj b c := by
      rw [SimpleGraph.fromEdgeSet_adj]
      constructor
      · simp [C]
      · exact hbc
    have hcaH : H.Adj c a := by
      rw [SimpleGraph.fromEdgeSet_adj]
      constructor
      · simp [C]
      · exact hac.symm
    let pbc : H.Walk b c := Walk.cons hbcH Walk.nil
    have hpbc : pbc.IsPath := by
      apply Walk.IsPath.cons Walk.IsPath.nil
      simp [hbc]
    let p : H.Walk b a := pbc.concat hcaH
    have hp : p.IsPath := by
      apply Walk.IsPath.concat hpbc
      simp [pbc, hab, hac]
    let cyc : H.Walk a a := Walk.cons habH p
    have hcyc : cyc.IsCycle := by
      apply (Walk.cons_isCycle_iff p habH).mpr
      refine ⟨hp, ?_⟩
      simp [p, pbc, hab, hac, hbc]
    exact hforest.2 cyc hcyc
  refine ⟨?_, hnotforest, ?_⟩
  · simpa [C] using hCground
  · intro e he
    apply isGraphForest_of_card_le_two
    · intro f hf
      exact hCground (Finset.mem_of_mem_erase hf)
    · have heC : e ∈ C := by simpa [C] using he
      rw [Finset.card_erase_of_mem heC, hCcard]

lemma hardSphere_nbc_region_excludes_fork_chord
    {k : Nat} [NeZero k] (r : HardSphereConfiguration k 3)
    {T : Finset (Sym2 (Fin k))} {a b c : Fin k}
    (hr : r ∈ nbcRegion (V := Fin k)
      (hardSphereActiveExact (k := k) (d := 3)) T)
    (hf : hardSphereFork T a b c)
    (hbc : ‖hardSpherePosition r b - hardSpherePosition r c‖ < (1 : ℝ)) :
    False := by
  change IsExplicitNBCTree (overlapGraph (hardSphereActiveExact r)) T at hr
  have hforest := hr.1
  have hab : a ≠ b := ne_of_lt hf.1
  have hbcne : b ≠ c := ne_of_lt hf.2.1
  have hac : a ≠ c := ne_of_lt (lt_trans hf.1 hf.2.1)
  have habG : s(a, b) ∈ (overlapGraph (hardSphereActiveExact r)).edgeSet := by
    apply hforest.1
    simpa using hf.2.2.1
  have hacG : s(a, c) ∈ (overlapGraph (hardSphereActiveExact r)).edgeSet := by
    apply hforest.1
    simpa using hf.2.2.2
  have hbcG : s(b, c) ∈ (overlapGraph (hardSphereActiveExact r)).edgeSet := by
    rw [edgeSet_overlapGraph]
    simp only [Finset.mem_coe, activeEdgeFinset, Finset.mem_filter,
      Finset.mem_univ, true_and]
    refine ⟨?_, ?_⟩
    · apply mem_graphEdgeFinset.mpr
      simp [hbcne]
    · rw [hardSphereActiveExact_mk, decide_eq_true_eq]
      exact hbc
  let C : Finset (Sym2 (Fin k)) := {s(a, b), s(a, c), s(b, c)}
  have hC : IsGraphCircuit (overlapGraph (hardSphereActiveExact r)) C := by
    simpa [C] using isGraphTriangleCircuit hab hac hbcne habG hacG hbcG
  have hmax : ∀ e ∈ C, graphEdgeLE e s(b, c) := by
    intro e he
    simp only [C, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact hardSphereEdgeLE_fork_chord hf.1 hf.2.1
    · exact hardSphereEdgeLE_fork_member hf.1 hf.2.1
    · simp [graphEdgeLE]
  have hsub : ((C.erase s(b, c) : Finset (Sym2 (Fin k))) : Set (Sym2 (Fin k))) ⊆
      (T : Set (Sym2 (Fin k))) := by
    intro e he
    have heC : e ∈ C := Finset.mem_of_mem_erase he
    simp only [C, Finset.mem_insert, Finset.mem_singleton] at heC
    rcases heC with rfl | rfl | rfl
    · exact hf.2.2.1
    · exact hf.2.2.2
    · simp at he
  apply hr.2.2
  exact ⟨s(b, c), C, hC, by simp [C], hmax, hsub⟩



/-- The volume of the open unit ball in the three-dimensional position space. -/
def hardSphereKappa : ℝ :=
  let : Fintype (Fin 3) := Fin.fintype 3
  (volume : Measure (HSPosition 3)).real (ball (0 : HSPosition 3) 1)

lemma hardSphereKappa_eq : hardSphereKappa = 4 * Real.pi / 3 := by
  unfold hardSphereKappa
  change (volume (ball (0 : HSPosition 3) 1)).toReal = 4 * Real.pi / 3
  rw [EuclideanSpace.volume_ball_fin_three]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (1 : ℝ)),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi * 4 / 3)]
  ring

/-- The hard-sphere configuration region owned by a fixed edge set. -/
def hardSphereTreeRegion {k : Nat} [NeZero k]
    (T : Finset (Sym2 (Fin k))) : Set (HardSphereConfiguration k 3) :=
  {r | ∀ e ∈ T, hardSphereActiveExact r e = true}

/-- The part of a tree region where the two leaves of an order-compatible fork
are also within range. -/
def hardSphereForkEvent {k : Nat} [NeZero k]
    (T : Finset (Sym2 (Fin k))) (_a b c : Fin k) : Set (HardSphereConfiguration k 3) :=
  hardSphereTreeRegion T ∩ {r |
    ‖hardSpherePosition r b - hardSpherePosition r c‖ < (1 : ℝ)}

lemma measurableSet_hardSphereTreeRegion {k : Nat} [NeZero k]
    (T : Finset (Sym2 (Fin k))) :
    MeasurableSet (hardSphereTreeRegion T) := by
  rw [show hardSphereTreeRegion T =
      ⋂ e ∈ T, {r : HardSphereConfiguration k 3 |
        hardSphereActiveExact r e = true} by
    ext r
    simp [hardSphereTreeRegion]]
  exact T.measurableSet_biInter (fun e he =>
    measurableSet_preimage (measurable_hardSphereActiveExact_edge e)
      (measurableSet_singleton true))

lemma measurableSet_hardSphereForkEvent {k : Nat} [NeZero k]
    (T : Finset (Sym2 (Fin k))) (a b c : Fin k) :
    MeasurableSet (hardSphereForkEvent T a b c) := by
  apply (measurableSet_hardSphereTreeRegion T).inter
  change MeasurableSet ((fun r : HardSphereConfiguration k 3 =>
    ‖hardSpherePosition r b - hardSpherePosition r c‖) ⁻¹' Iio (1 : ℝ))
  apply MeasurableSet.preimage measurableSet_Iio
  exact (continuous_norm.comp
    ((continuous_hardSpherePosition b).sub
      (continuous_hardSpherePosition c))).measurable

lemma hardSphere_nbc_region_subset_tree_region
    {k : Nat} [NeZero k]
    {r : HardSphereConfiguration k 3}
    {T : Finset (Sym2 (Fin k))}
    (hr : r ∈ nbcRegion (V := Fin k)
      (hardSphereActiveExact (k := k) (d := 3)) T) :
    r ∈ hardSphereTreeRegion T := by
  intro e he
  have heG : e ∈ (overlapGraph (hardSphereActiveExact r)).edgeSet := by
    exact hr.1.1 (by simpa using he)
  rw [edgeSet_overlapGraph] at heG
  have heactive : activeEdge (hardSphereActiveExact r) e := by
    simpa [activeEdgeFinset] using heG
  exact heactive.2

lemma hardSphere_forkEvent_subset_treeRegion
    {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))} {a b c : Fin k} :
    hardSphereForkEvent T a b c ⊆ hardSphereTreeRegion T := by
  intro r hr
  exact hr.1

lemma hardSphere_nbc_region_disjoint_forkEvent
    {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))} {a b c : Fin k}
    (hf : hardSphereFork T a b c) :
    Disjoint
      (nbcRegion (V := Fin k)
        (hardSphereActiveExact (k := k) (d := 3)) T)
      (hardSphereForkEvent T a b c) := by
  rw [Set.disjoint_left]
  intro r hrN hrF
  exact hardSphere_nbc_region_excludes_fork_chord r hrN hf hrF.2

end

end HsVirial
