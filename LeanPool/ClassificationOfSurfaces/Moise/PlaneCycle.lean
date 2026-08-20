/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.PolygonalArc

/-!
# Polygonal circles from cycles in finite plane complexes

A simple graph cycle in the one-skeleton of a finite plane complex is automatically a
polygonal circle.  The exact segment-intersection axioms follow from the complex's face-to-face
law and the fact that a simple cycle has no repeated cyclic vertex.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace PlaneComplex

variable (K : PlaneComplex) {v : K.Vertex}

/-- The geometric segment carried by an edge of the vertex graph. -/
theorem cellCarrier_pair_of_adj {u w : K.Vertex} (_ : K.vertexGraph.Adj u w) :
    K.cellCarrier {u, w} = segment ℝ (K.position u) (K.position w) := by
  rw [PlaneComplex.cellCarrier]
  have himage : K.position ''
      (({u, w} : Finset K.Vertex) : Set K.Vertex) =
      {K.position u, K.position w} := by
    ext x
    simp [eq_comm]
  rw [himage, convexHull_pair]

/-- A graph walk traces a canonical geometric path through the corresponding straight edges. -/
noncomputable def walkGeometricPath {u w : K.Vertex}
    (p : K.vertexGraph.Walk u w) : Path (K.position u) (K.position w) := by
  induction p with
  | nil => exact Path.refl _
  | cons h p ih =>
      exact (Path.segment (K.position _) (K.position _)).trans ih

@[simp] theorem walkGeometricPath_nil (u : K.Vertex) :
    K.walkGeometricPath (SimpleGraph.Walk.nil : K.vertexGraph.Walk u u) =
      Path.refl (K.position u) := rfl

@[simp] theorem walkGeometricPath_cons {u w z : K.Vertex}
    (h : K.vertexGraph.Adj u w) (p : K.vertexGraph.Walk w z) :
    K.walkGeometricPath (SimpleGraph.Walk.cons h p) =
      (Path.segment (K.position u) (K.position w)).trans
        (K.walkGeometricPath p) := rfl

/-- The geometric path of a walk stays in the support of the complex, provided its final vertex
is an actual zero-face. -/
theorem range_walkGeometricPath_subset_support {u w : K.Vertex}
    (p : K.vertexGraph.Walk u w)
    (hw : ({w} : Finset K.Vertex) ∈ K.simplexes) :
    Set.range (K.walkGeometricPath p) ⊆ K.support := by
  induction p with
  | nil =>
      rw [K.walkGeometricPath_nil, Path.refl_range]
      rintro x rfl
      exact K.cellCarrier_subset_support hw
        (by simp [PlaneComplex.cellCarrier])
  | cons h p ih =>
      rw [K.walkGeometricPath_cons, Path.trans_range, Path.range_segment,
        ← K.cellCarrier_pair_of_adj h]
      exact Set.union_subset
        (K.cellCarrier_subset_support h.2) (ih hw)

/-- Every straight edge of a walk occurs in the range of its geometric path. -/
theorem walkSegment_subset_range {u w : K.Vertex} (p : K.vertexGraph.Walk u w)
    (i : Fin p.length) :
    segment ℝ (K.position (p.getVert i.val))
        (K.position (p.getVert (i.val + 1))) ⊆
      Set.range (K.walkGeometricPath p) := by
  induction p with
  | nil => exact Fin.elim0 i
  | @cons u z w h p ih =>
      cases i using Fin.cases with
      | zero =>
          rw [K.walkGeometricPath_cons, Path.trans_range]
          apply Set.subset_union_of_subset_left
          rw [Path.range_segment]
          simp
      | succ i =>
          rw [K.walkGeometricPath_cons, Path.trans_range]
          apply Set.subset_union_of_subset_right
          simpa only [Fin.val_succ, SimpleGraph.Walk.getVert_cons_succ,
            Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih i

/-- A nonconstant walk's geometric path is covered by its finitely many straight edges. -/
theorem exists_walkSegment_of_mem_range {u w : K.Vertex}
    (p : K.vertexGraph.Walk u w) (hp : 0 < p.length) {x : Plane}
    (hx : x ∈ Set.range (K.walkGeometricPath p)) :
    ∃ i : Fin p.length,
      x ∈ segment ℝ (K.position (p.getVert i.val))
        (K.position (p.getVert (i.val + 1))) := by
  induction p with
  | nil => simp at hp
  | @cons u z w h p ih =>
      rw [K.walkGeometricPath_cons, Path.trans_range] at hx
      rcases hx with hxFirst | hxTail
      · refine ⟨⟨0, by simp⟩, ?_⟩
        simpa only [Path.range_segment, SimpleGraph.Walk.getVert_zero,
          SimpleGraph.Walk.getVert_cons_succ] using hxFirst
      · by_cases hzero : p.length = 0
        · cases p with
          | nil =>
              refine ⟨⟨0, by simp⟩, ?_⟩
              rw [K.walkGeometricPath_nil, Path.refl_range] at hxTail
              have hxz : x = K.position z := Set.mem_singleton_iff.mp hxTail
              simpa only [hxz, SimpleGraph.Walk.getVert_zero,
                SimpleGraph.Walk.getVert_cons_succ] using
                  (right_mem_segment ℝ (K.position u) (K.position z))
          | cons h' q => simp at hzero
        · obtain ⟨i, hi⟩ := ih (Nat.pos_of_ne_zero hzero) hxTail
          refine ⟨i.succ, ?_⟩
          simpa only [Fin.val_succ, SimpleGraph.Walk.getVert_cons_succ,
            Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hi

/-- Concatenating graph walks unions the ranges of their canonical geometric paths. -/
theorem range_walkGeometricPath_append {u v w : K.Vertex}
    (p : K.vertexGraph.Walk u v) (q : K.vertexGraph.Walk v w) :
    Set.range (K.walkGeometricPath (p.append q)) =
      Set.range (K.walkGeometricPath p) ∪ Set.range (K.walkGeometricPath q) := by
  induction p with
  | nil =>
      rw [SimpleGraph.Walk.nil_append, K.walkGeometricPath_nil, Path.refl_range]
      apply Set.Subset.antisymm Set.subset_union_right
      exact Set.union_subset
        (Set.singleton_subset_iff.mpr (Path.source_mem_range (K.walkGeometricPath q)))
        Set.Subset.rfl
  | cons h p ih =>
      rw [SimpleGraph.Walk.cons_append, K.walkGeometricPath_cons,
        K.walkGeometricPath_cons, Path.trans_range, Path.trans_range, ih,
        Set.union_assoc]

/-- Changing only a walk's dependent endpoint witnesses does not change its geometric range. -/
theorem range_walkGeometricPath_copy {u v u' v' : K.Vertex}
    (p : K.vertexGraph.Walk u v) (hu : u = u') (hv : v = v') :
    Set.range (K.walkGeometricPath (p.copy hu hv)) =
      Set.range (K.walkGeometricPath p) := by
  subst u'
  subst v'
  rfl

/-- Mapping a walk from a carrier restriction back to the ambient plane complex preserves its
geometric range. -/
theorem range_walkGeometricPath_mapLe_restrictedTo (C : Set Plane)
    {u v : (K.restrictedTo C).Vertex}
    (p : (K.restrictedTo C).vertexGraph.Walk u v)
    (hle : (K.restrictedTo C).vertexGraph ≤ K.vertexGraph) :
    Set.range (K.walkGeometricPath (p.mapLe hle)) =
      Set.range ((K.restrictedTo C).walkGeometricPath p) := by
  let p' : K.vertexGraph.Walk u v :=
    @SimpleGraph.Walk.mapLe K.Vertex (K.restrictedTo C).vertexGraph K.vertexGraph hle u v p
  change Set.range (K.walkGeometricPath p') =
    Set.range ((K.restrictedTo C).walkGeometricPath p)
  by_cases hzero : p.length = 0
  · cases p with
    | nil => rfl
    | cons h q => simp at hzero
  · have hpos : 0 < p.length := Nat.pos_of_ne_zero hzero
    have hlength : p'.length = p.length := by
      change (SimpleGraph.Walk.map (.ofLE hle) p).length = p.length
      exact SimpleGraph.Walk.length_map (.ofLE hle) p
    have hmap (n : ℕ) : p'.getVert n = p.getVert n := by
      change (SimpleGraph.Walk.map (.ofLE hle) p).getVert n = p.getVert n
      exact (SimpleGraph.Walk.getVert_map (.ofLE hle) p n).trans
        (SimpleGraph.Hom.ofLE_apply hle (p.getVert n))
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨i, hi⟩ := K.exists_walkSegment_of_mem_range p'
        (by simpa [hlength] using hpos) hx
      let j : Fin p.length := ⟨i.val, by simpa [hlength] using i.isLt⟩
      apply (K.restrictedTo C).walkSegment_subset_range p j
      rw [hmap i.val, hmap (i.val + 1)] at hi
      simpa [j] using hi
    · intro x hx
      obtain ⟨i, hi⟩ := (K.restrictedTo C).exists_walkSegment_of_mem_range p hpos hx
      let j : Fin p'.length := ⟨i.val, by simpa only [hlength] using i.isLt⟩
      apply K.walkSegment_subset_range p' j
      rw [hmap i.val, hmap (i.val + 1)]
      exact hi

end PlaneComplex

/-- Change only the endpoint witnesses of a path.  Its underlying function, and hence its range
and injectivity, are unchanged. -/
def Path.copy {X : Type*} [TopologicalSpace X] {a b a' b' : X}
    (p : Path a b) (ha : a = a') (hb : b = b') : Path a' b' where
  toFun := p
  continuous_toFun := p.continuous
  source' := p.source.trans ha
  target' := p.target.trans hb

@[simp] theorem Path.copy_apply {X : Type*} [TopologicalSpace X] {a b a' b' : X}
    (p : Path a b) (ha : a = a') (hb : b = b') (t : unitInterval) :
    Path.copy p ha hb t = p t := rfl

@[simp] theorem Path.copy_range {X : Type*} [TopologicalSpace X] {a b a' b' : X}
    (p : Path a b) (ha : a = a') (hb : b = b') :
    Set.range (Path.copy p ha hb) = Set.range p := rfl

/-- A path contained in an embedded arc and joining the same endpoints covers that entire arc.
This is the order-convexity of connected subsets of the unit interval, transported through the
arc homeomorphism. -/
theorem Path.range_eq_of_subset_of_injective {X : Type*} [TopologicalSpace X] [T2Space X]
    {a b : X} (arc path : Path a b) (harc : Function.Injective arc)
    (hsub : Set.range path ⊆ Set.range arc) :
    Set.range path = Set.range arc := by
  apply Set.Subset.antisymm hsub
  let e₀ : unitInterval ≃ Set.range arc := Equiv.ofInjective arc harc
  let e : unitInterval ≃ₜ Set.range arc :=
    Continuous.homeoOfEquivCompactToT2
      (f := e₀) (Continuous.subtype_mk arc.continuous fun t => ⟨t, rfl⟩)
  let R : Set (Set.range arc) := {x | x.1 ∈ Set.range path}
  have hvalR : ((↑) : Set.range arc → X) '' R = Set.range path := by
    apply Set.Subset.antisymm
    · rintro x ⟨y, hy, rfl⟩
      exact hy
    · intro x hx
      exact ⟨⟨x, hsub hx⟩, hx, rfl⟩
  have hR : IsPreconnected R := by
    rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, hvalR]
    exact (isConnected_range path.continuous).isPreconnected
  have hpre : IsPreconnected (e ⁻¹' R) :=
    e.isPreconnected_preimage.mpr hR
  have hzero : (0 : unitInterval) ∈ e ⁻¹' R := by
    change (e 0).1 ∈ Set.range path
    change arc 0 ∈ Set.range path
    rw [arc.source]
    exact Path.source_mem_range path
  have hone : (1 : unitInterval) ∈ e ⁻¹' R := by
    change (e 1).1 ∈ Set.range path
    change arc 1 ∈ Set.range path
    rw [arc.target]
    exact Path.target_mem_range path
  have hord : Set.OrdConnected (e ⁻¹' R) :=
    isPreconnected_iff_ordConnected.mp hpre
  intro x hx
  obtain ⟨t, rfl⟩ := hx
  have ht : t ∈ Set.Icc (0 : unitInterval) 1 := ⟨t.2.1, t.2.2⟩
  have htpre := hord.out hzero hone ht
  change (e t).1 ∈ Set.range path at htpre
  exact htpre

namespace PlaneComplex

variable (K : PlaneComplex) {v : K.Vertex}

private theorem cycle_index_injective (p : K.vertexGraph.Walk v v) (hp : p.IsCycle) :
    Function.Injective (fun i : ZMod p.length => p.getVert i.val) := by
  have hn : 0 < p.length := lt_of_lt_of_le (by omega) hp.three_le_length
  letI : NeZero p.length := ⟨hn.ne'⟩
  intro i j hij
  apply ZMod.val_injective
  apply hp.getVert_injOn'
  · simp only [Set.mem_setOf_eq]
    exact Nat.le_sub_one_of_lt i.val_lt
  · simp only [Set.mem_setOf_eq]
    exact Nat.le_sub_one_of_lt j.val_lt
  · exact hij

private theorem cycle_index_ne_next (p : K.vertexGraph.Walk v v) (hp : p.IsCycle)
    (i : ZMod p.length) : i ≠ i + 1 := by
  have hn : 0 < p.length := lt_of_lt_of_le (by omega) hp.three_le_length
  letI : NeZero p.length := ⟨hn.ne'⟩
  intro hi
  have hzero : (0 : ZMod p.length) = 1 := by
    calc
      0 = i - i := by abel
      _ = (i + 1) - i := congrArg (fun z => z - i) hi
      _ = 1 := by abel
  have hval := congrArg ZMod.val hzero
  have hone : (1 : ZMod p.length).val = 1 := by
    have hn3 := hp.three_le_length
    letI : Fact ((1 : ℕ) < p.length) := ⟨by omega⟩
    exact ZMod.val_one p.length
  rw [ZMod.val_zero, hone] at hval
  omega

private theorem cycle_index_ne_add_two (p : K.vertexGraph.Walk v v) (hp : p.IsCycle)
    (i : ZMod p.length) : i ≠ i + 2 := by
  have hn : 0 < p.length := lt_of_lt_of_le (by omega) hp.three_le_length
  letI : NeZero p.length := ⟨hn.ne'⟩
  intro hi
  have hzero : (0 : ZMod p.length) = 2 := by
    calc
      0 = i - i := by abel
      _ = (i + 2) - i := congrArg (fun z => z - i) hi
      _ = 2 := by abel
  have hval := congrArg ZMod.val hzero
  have htwo : (2 : ZMod p.length).val = 2 := by
    change ((2 : ℕ) : ZMod p.length).val = 2
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt hp.three_le_length
  rw [ZMod.val_zero, htwo] at hval
  omega

private theorem cycle_next_val (p : K.vertexGraph.Walk v v) (hp : p.IsCycle)
    (i : ZMod p.length) :
    (i + 1).val = if i.val + 1 < p.length then i.val + 1 else 0 := by
  have hn : 0 < p.length := lt_of_lt_of_le (by omega) hp.three_le_length
  letI : NeZero p.length := ⟨hn.ne'⟩
  have hone : (1 : ZMod p.length).val = 1 := by
    have hn3 := hp.three_le_length
    letI : Fact ((1 : ℕ) < p.length) := ⟨by omega⟩
    exact ZMod.val_one p.length
  rw [ZMod.val_add, hone]
  split_ifs with hi
  · exact Nat.mod_eq_of_lt hi
  · have hil := i.val_lt
    have heq : i.val + 1 = p.length := by omega
    rw [heq, Nat.mod_self]

private theorem cycle_adj (p : K.vertexGraph.Walk v v) (hp : p.IsCycle)
    (i : ZMod p.length) :
    K.vertexGraph.Adj (p.getVert i.val) (p.getVert (i + 1).val) := by
  have hn : 0 < p.length := lt_of_lt_of_le (by omega) hp.three_le_length
  letI : NeZero p.length := ⟨hn.ne'⟩
  rw [cycle_next_val K p hp i]
  split_ifs with hi
  · exact p.adj_getVert_succ i.val_lt
  · have hil := i.val_lt
    have heq : i.val + 1 = p.length := by omega
    have hadj := p.adj_getVert_succ i.val_lt
    rw [heq, p.getVert_length] at hadj
    simpa using hadj

private theorem cycle_edge_face (p : K.vertexGraph.Walk v v) (hp : p.IsCycle)
    (i : ZMod p.length) :
    ({p.getVert i.val, p.getVert (i + 1).val} : Finset K.Vertex) ∈ K.simplexes :=
  (cycle_adj K p hp i).2

private theorem cycle_edge_carrier (p : K.vertexGraph.Walk v v) (_ : p.IsCycle)
    (i : ZMod p.length) :
    K.cellCarrier {p.getVert i.val, p.getVert (i + 1).val} =
      segment ℝ (K.position (p.getVert i.val))
        (K.position (p.getVert (i + 1).val)) := by
  rw [PlaneComplex.cellCarrier]
  have himage : K.position ''
      (({p.getVert i.val, p.getVert (i + 1).val} : Finset K.Vertex) : Set K.Vertex) =
      {K.position (p.getVert i.val), K.position (p.getVert (i + 1).val)} := by
    ext x
    simp [eq_comm]
  rw [himage, convexHull_pair]

private theorem cycle_edge_inter_next (p : K.vertexGraph.Walk v v) (hp : p.IsCycle)
    (i : ZMod p.length) :
    ({p.getVert i.val, p.getVert (i + 1).val} : Finset K.Vertex) ∩
        {p.getVert (i + 1).val, p.getVert (i + 2).val} =
      {p.getVert (i + 1).val} := by
  have hinj := cycle_index_injective K p hp
  have hi1 : p.getVert i.val ≠ p.getVert (i + 1).val :=
    fun h => cycle_index_ne_next K p hp i (hinj h)
  have hi2 : p.getVert i.val ≠ p.getVert (i + 2).val :=
    fun h => cycle_index_ne_add_two K p hp i (hinj h)
  ext w
  simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hwi | hwi, hwnext | hwtwo⟩
    · exact (hi1 (hwi.symm.trans hwnext)).elim
    · exact (hi2 (hwi.symm.trans hwtwo)).elim
    · exact hwi
    · exact hwi
  · intro hw
    exact ⟨Or.inr hw, Or.inl hw⟩

/-- A simple cycle in a finite plane complex determines an honest polygonal circle. -/
noncomputable def polygonalCircleOfCycle (p : K.vertexGraph.Walk v v) (hp : p.IsCycle) :
    PolygonalCircle := by
  have hn : 0 < p.length := lt_of_lt_of_le (by omega) hp.three_le_length
  letI : NeZero p.length := ⟨hn.ne'⟩
  let point : ZMod p.length → Plane := fun i => K.position (p.getVert i.val)
  refine {
    n := p.length
    three_le := hp.three_le_length
    vertex := point
    adjacent_ne := ?_
    consecutive_inter := ?_
    nonadjacent_disjoint := ?_ }
  · intro i hpos
    exact (cycle_adj K p hp i).ne (K.position_injective hpos)
  · intro i
    change segment ℝ (K.position (p.getVert i.val))
        (K.position (p.getVert (i + 1).val)) ∩
      segment ℝ (K.position (p.getVert (i + 1).val))
        (K.position (p.getVert (i + 2).val)) =
      {K.position (p.getVert (i + 1).val)}
    rw [← cycle_edge_carrier K p hp i]
    have hnextCarrier := cycle_edge_carrier K p hp (i + 1)
    rw [show i + 1 + 1 = i + 2 by ring] at hnextCarrier
    rw [← hnextCarrier]
    have hface := K.face_inter _ (cycle_edge_face K p hp i) _
      (cycle_edge_face K p hp (i + 1))
    rw [show i + 1 + 1 = i + 2 by ring] at hface
    change K.cellCarrier _ ∩ K.cellCarrier _ = K.cellCarrier _ at hface
    rw [cycle_edge_inter_next K p hp i] at hface
    rw [hface, PlaneComplex.cellCarrier]
    have himage : K.position ''
        (({p.getVert (i + 1).val} : Finset K.Vertex) : Set K.Vertex) =
        {point (i + 1)} := by
      ext x
      simp [point]
    rw [himage, convexHull_singleton]
  · intro i j hij hiprev hjnext
    rw [← cycle_edge_carrier K p hp i, ← cycle_edge_carrier K p hp j]
    have hdis : Disjoint
        ({p.getVert i.val, p.getVert (i + 1).val} : Finset K.Vertex)
        {p.getVert j.val, p.getVert (j + 1).val} := by
      rw [Finset.disjoint_left]
      intro w hwI hwJ
      simp only [Finset.mem_insert, Finset.mem_singleton] at hwI hwJ
      have hinj := cycle_index_injective K p hp
      rcases hwI with hwi | hwi <;> rcases hwJ with hwj | hwj
      · exact hij (hinj (hwi.symm.trans hwj))
      · exact hiprev (hinj (hwi.symm.trans hwj))
      · exact hjnext (hinj (hwi.symm.trans hwj)).symm
      · exact hij (add_right_cancel (hinj (hwi.symm.trans hwj)))
    have hface := K.face_inter _ (cycle_edge_face K p hp i) _
      (cycle_edge_face K p hp j)
    rw [Finset.disjoint_iff_inter_eq_empty.mp hdis] at hface
    simpa [PlaneComplex.cellCarrier] using hface

/-- The polygonal carrier associated to a graph cycle is exactly the range of the canonical
piecewise-linear path around that cycle. -/
theorem polygonalCircleOfCycle_carrier_eq_range_walkGeometricPath
    (p : K.vertexGraph.Walk v v) (hp : p.IsCycle) :
    (K.polygonalCircleOfCycle p hp).carrier =
      Set.range (K.walkGeometricPath p) := by
  have hn : 0 < p.length := lt_of_lt_of_le (by omega) hp.three_le_length
  letI : NeZero p.length := ⟨hn.ne'⟩
  apply Set.Subset.antisymm
  · intro x hx
    change x ∈ ⋃ i : ZMod p.length,
      segment ℝ (K.position (p.getVert i.val))
        (K.position (p.getVert (i + 1).val)) at hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    rw [cycle_next_val K p hp i] at hi
    by_cases hnext : i.val + 1 < p.length
    · rw [if_pos hnext] at hi
      exact K.walkSegment_subset_range p ⟨i.val, i.val_lt⟩ hi
    · rw [if_neg hnext] at hi
      have hlast : i.val + 1 = p.length := by
        have := i.val_lt
        omega
      have hedge := K.walkSegment_subset_range p ⟨i.val, i.val_lt⟩
      rw [hlast, p.getVert_length] at hedge
      apply hedge
      simpa only [p.getVert_zero] using hi
  · intro x hx
    obtain ⟨i, hi⟩ := K.exists_walkSegment_of_mem_range p hn hx
    change x ∈ ⋃ j : ZMod p.length,
      segment ℝ (K.position (p.getVert j.val))
        (K.position (p.getVert (j + 1).val))
    let j : ZMod p.length := i.val
    refine Set.mem_iUnion.mpr ⟨j, ?_⟩
    have hj : j.val = i.val := by
      rw [show j = (i.val : ZMod p.length) by rfl, ZMod.val_natCast,
        Nat.mod_eq_of_lt i.isLt]
    rw [cycle_next_val K p hp j, hj]
    by_cases hnext : i.val + 1 < p.length
    · rw [if_pos hnext]
      exact hi
    · rw [if_neg hnext]
      have hlast : i.val + 1 = p.length := by
        have := i.isLt
        omega
      rw [hlast, p.getVert_length] at hi
      rw [p.getVert_zero]
      exact hi

end PlaneComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
