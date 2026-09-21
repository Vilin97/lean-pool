/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Data.List.Sort
import Mathlib.MeasureTheory.Integral.Bochner.Set
import LeanPool.BKARForestFormula.BKAR.CubePartition.Orders

/-! # The unit cube and its ordered sectors

Defines the unit cube `[0,1]^{E(F)}` of a forest's edge parameters and, for
each enumeration of the edge set, the closed ordered sector
`orderedCubeSimplex` of parameter points whose coordinates decrease along
that order.  Proves that ordered-simplex parameter lists land in the
matching sector and that the sectors cover the cube: the unit cube is the
union of its canonical ordered sectors.  This is the set-level part of the
unit-cube partition step, which folds per-order sectors into the single
cube integral of the BKAR forest interpolation formula (see
`BKAR.Formula`).
-/

noncomputable section

namespace BKAR

namespace Forest

variable {V : Type*} [Fintype V] [DecidableEq V]

/--
The parameter cube `[0, 1]^{E(F)}` for a forest.  Parameters are indexed by
the edge subtype `F.EdgeParam`.
-/
def unitCube (F : Forest V) : Set (F.EdgeParam → ℝ) :=
  Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1

theorem mem_unitCube_iff (F : Forest V) (u : F.EdgeParam → ℝ) :
    u ∈ F.unitCube ↔ ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1 := by
  rw [unitCube]
  simp only [Set.mem_univ, Set.mem_pi, Set.mem_Icc, forall_const]

/--
The ordered simplex sector inside the unit cube attached to one edge order.
For `order = [e₁, ..., eₙ]`, this is the region
`1 ≥ u(e₁) ≥ ... ≥ u(eₙ) ≥ 0`, together with the ambient cube bounds.
-/
def orderedCubeSimplex (F : Forest V) (order : List (Edge V)) :
    Set (F.EdgeParam → ℝ) :=
  {u | u ∈ F.unitCube ∧
    OrderedSimplexParams 1 (order.map (F.paramValue u))}

theorem mem_orderedCubeSimplex_iff
    (F : Forest V) (order : List (Edge V)) (u : F.EdgeParam → ℝ) :
    u ∈ F.orderedCubeSimplex order ↔
      u ∈ F.unitCube ∧
        OrderedSimplexParams 1 (order.map (F.paramValue u)) :=
  Iff.rfl

theorem orderedCubeSimplex_subset_unitCube
    (F : Forest V) (order : List (Edge V)) :
    F.orderedCubeSimplex order ⊆ F.unitCube := by
  intro u hu
  exact hu.1

theorem orderedCubeSimplex_nil (F : Forest V) :
    F.orderedCubeSimplex [] = F.unitCube := by
  ext u
  simp [orderedCubeSimplex]

/--
Any ordered-simplex coordinate list gives a point of the unit cube through
`paramsOfOrder`. Coordinates not represented in the list use the default `0`.
-/
theorem paramsOfOrder_mem_unitCube_of_orderedSimplexParams
    (F : Forest V) (order : List (Edge V)) {ts : List ℝ}
    (hts : OrderedSimplexParams 1 ts) :
    F.paramsOfOrder order ts ∈ F.unitCube := by
  rw [mem_unitCube_iff]
  intro e
  rw [paramsOfOrder]
  by_cases hidx : order.idxOf e.val < ts.length
  · rw [List.getD_eq_getElem _ _ hidx]
    constructor
    · exact OrderedSimplexParams.nonneg_of_mem hts
        (List.getElem_mem hidx)
    · exact OrderedSimplexParams.le_top_of_mem hts
        (List.getElem_mem hidx)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hidx)]
    norm_num

/--
Reading back the parameters of a nodup order from `paramsOfOrder` recovers the
original coordinate list, provided the list lengths match.
-/
theorem map_paramValue_paramsOfOrder_eq_of_nodup_of_forall_mem
    (F : Forest V) :
    ∀ (order : List (Edge V)) {ts : List ℝ},
      order.Nodup →
      (∀ e ∈ order, e ∈ F.edges) →
      ts.length = order.length →
      order.map (F.paramValue (F.paramsOfOrder order ts)) = ts
  | [], ts, _hnodup, _hmem, hlen => by
      have hts : ts = [] := List.length_eq_zero_iff.mp hlen
      rw [hts]
      rfl
  | e :: order, [], _hnodup, _hmem, hlen => by
      simp at hlen
  | e :: order, t :: ts, hnodup, hmem, hlen => by
      have he : e ∈ F.edges := hmem e (by simp)
      have hnotMem : e ∉ order := (List.nodup_cons.mp hnodup).1
      have htailNodup : order.Nodup := (List.nodup_cons.mp hnodup).2
      have htailMem : ∀ e' ∈ order, e' ∈ F.edges := by
        intro e' he'
        exact hmem e' (List.mem_cons_of_mem e he')
      have htailLen : ts.length = order.length := by
        simpa using hlen
      have htailMap :
          order.map (F.paramValue (F.paramsOfOrder (e :: order) (t :: ts))) =
            order.map (F.paramValue (F.paramsOfOrder order ts)) := by
        apply List.map_congr_left
        intro e' he'
        have he'F : e' ∈ F.edges := htailMem e' he'
        have hne : e' ≠ e := by
          intro h
          exact hnotMem (h ▸ he')
        rw [F.paramValue_of_mem _ he'F, F.paramValue_of_mem _ he'F]
        exact F.paramsOfOrder_cons_of_ne order t ts he'F hne
      rw [List.map_cons]
      rw [F.paramValue_of_mem _ he]
      rw [F.paramsOfOrder_cons_self e order t ts he]
      rw [htailMap]
      rw [map_paramValue_paramsOfOrder_eq_of_nodup_of_forall_mem
        F order htailNodup htailMem htailLen]

/--
For a canonical edge order, `paramsOfOrder` is a right inverse to the sector
coordinate readback map.
-/
theorem map_paramValue_paramsOfOrder_eq_of_mem_edgeOrders
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders)
    {ts : List ℝ} (hlen : ts.length = order.length) :
    order.map (F.paramValue (F.paramsOfOrder order ts)) = ts := by
  exact
    F.map_paramValue_paramsOfOrder_eq_of_nodup_of_forall_mem order
      (F.nodup_of_mem_edgeOrders horder)
      (by
        intro e he
        have hset := F.toFinset_eq_of_mem_edgeOrders horder
        rw [← hset]
        exact List.mem_toFinset.mpr he)
      hlen

/--
Set-level simplex-sector bridge: ordered-simplex coordinates, sent into cube
coordinates
by `paramsOfOrder`, land in the ordered cube sector for the same canonical
edge order.
-/
theorem paramsOfOrder_mem_orderedCubeSimplex_of_mem_edgeOrders
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders)
    {ts : List ℝ} (hts : OrderedSimplexParams 1 ts)
    (hlen : ts.length = order.length) :
    F.paramsOfOrder order ts ∈ F.orderedCubeSimplex order := by
  rw [mem_orderedCubeSimplex_iff]
  constructor
  · exact F.paramsOfOrder_mem_unitCube_of_orderedSimplexParams order hts
  · rw [F.map_paramValue_paramsOfOrder_eq_of_mem_edgeOrders horder hlen]
    exact hts

/--
If an edge order is pairwise sorted in descending parameter value and every
listed value lies in `[0, top]`, then the readback value list is an ordered
simplex.
-/
theorem orderedSimplexParams_map_paramValue_of_pairwise_ge
    (F : Forest V) (u : F.EdgeParam → ℝ) :
    ∀ (order : List (Edge V)) (top : ℝ),
      order.Pairwise (fun e e' => F.paramValue u e' ≤ F.paramValue u e) →
      (∀ e ∈ order, 0 ≤ F.paramValue u e) →
      (∀ e ∈ order, F.paramValue u e ≤ top) →
      OrderedSimplexParams top (order.map (F.paramValue u))
  | [], top, _hpair, _hnonneg, _hleTop => by
      exact orderedSimplexParams_nil top
  | e :: order, top, hpair, hnonneg, hleTop => by
      rw [List.map_cons, orderedSimplexParams_cons]
      constructor
      · exact hnonneg e (by simp)
      constructor
      · exact hleTop e (by simp)
      · exact
          orderedSimplexParams_map_paramValue_of_pairwise_ge F u order
            (F.paramValue u e) (List.pairwise_cons.mp hpair).2
            (by
              intro e' he'
              exact hnonneg e' (List.mem_cons_of_mem e he'))
            (by
              intro e' he'
              exact (List.pairwise_cons.mp hpair).1 e' he')

/--
Set-level cube cover for the unit-cube partition step: every point of the
unit cube lies in at least one
ordered cube sector indexed by a canonical edge order.
-/
theorem exists_mem_edgeOrders_and_mem_orderedCubeSimplex_of_mem_unitCube
    (F : Forest V) {u : F.EdgeParam → ℝ} (hu : u ∈ F.unitCube) :
    ∃ order : List (Edge V),
      order ∈ F.edgeOrders ∧ u ∈ F.orderedCubeSimplex order := by
  classical
  let r : Edge V → Edge V → Prop :=
    fun e e' => F.paramValue u e' ≤ F.paramValue u e
  have : DecidableRel r := Classical.decRel r
  have : IsTrans (Edge V) r := ⟨fun _ _ _ hab hbc => hbc.trans hab⟩
  have : Std.Total r := ⟨fun e e' =>
    le_total (F.paramValue u e') (F.paramValue u e)⟩
  let order : List (Edge V) := F.edges.toList.mergeSort (r · ·)
  refine ⟨order, ?_, ?_⟩
  · exact (F.mem_edgeOrders_iff).mpr (List.mergeSort_perm F.edges.toList (r · ·))
  · rw [mem_orderedCubeSimplex_iff]
    constructor
    · exact hu
    · have hpair : order.Pairwise r := by
        exact List.pairwise_mergeSort' r F.edges.toList
      exact
        orderedSimplexParams_map_paramValue_of_pairwise_ge F u order 1
          hpair
          (by
            intro e he
            exact
              (F.paramValue_mem_Icc u ((mem_unitCube_iff F u).mp hu) e).1)
          (by
            intro e he
            exact
              (F.paramValue_mem_Icc u ((mem_unitCube_iff F u).mp hu) e).2)

/-- The ordered cube sectors cover the unit cube. -/
theorem unitCube_subset_iUnion_orderedCubeSimplex (F : Forest V) :
    F.unitCube ⊆
      ⋃ order : {order : List (Edge V) // order ∈ F.edgeOrders},
        F.orderedCubeSimplex order.val := by
  intro u hu
  rcases F.exists_mem_edgeOrders_and_mem_orderedCubeSimplex_of_mem_unitCube
      hu with
    ⟨order, horder, hsector⟩
  rw [Set.mem_iUnion]
  exact ⟨⟨order, horder⟩, hsector⟩

/-- Every ordered cube sector is contained in the unit cube. -/
theorem iUnion_orderedCubeSimplex_subset_unitCube (F : Forest V) :
    (⋃ order : {order : List (Edge V) // order ∈ F.edgeOrders},
        F.orderedCubeSimplex order.val) ⊆ F.unitCube := by
  intro u hu
  rw [Set.mem_iUnion] at hu
  rcases hu with ⟨order, hsector⟩
  exact F.orderedCubeSimplex_subset_unitCube order.val hsector

/--
Set-level partition cover: the unit cube is the union of its canonical
ordered cube sectors. Pairwise disjointness only holds away from coordinate
collision hyperplanes, which is the remaining measure-zero part of the
unit-cube partition step.
-/
theorem unitCube_eq_iUnion_orderedCubeSimplex (F : Forest V) :
    F.unitCube =
      ⋃ order : {order : List (Edge V) // order ∈ F.edgeOrders},
        F.orderedCubeSimplex order.val :=
  Set.Subset.antisymm
    (F.unitCube_subset_iUnion_orderedCubeSimplex)
    (F.iUnion_orderedCubeSimplex_subset_unitCube)

/--
The usual unordered BKAR cube contribution for one `Forest` representative, using the
mixed partial attached to `F.edges.toList`.
-/
def cubeContribution (F : Forest V) (ρ : (Edge V → ℝ) → ℝ) : ℝ :=
  ∫ u in F.unitCube, F.mixedPartial ρ (F.standardInterp u)

/--
The set-integral version of one ordered cube sector.  The later cube-partition
bridge identifies the sum of these sectors with `cubeContribution`; the
ordered-simplex bridge identifies each sector with `orderedContribution`.
-/
def orderedCubeSectorContribution
    (F : Forest V) (order : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ) : ℝ :=
  ∫ u in F.orderedCubeSimplex order,
    mixedPartialList order.reverse ρ (F.standardInterp u)

end Forest

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
